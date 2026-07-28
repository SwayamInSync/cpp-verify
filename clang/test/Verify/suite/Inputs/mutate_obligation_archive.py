import argparse
import struct


class Archive:
    def __init__(self, data):
        self.data = bytearray(data)
        self.offset = 0
        self.flags = 0
        self.feature_offsets = []
        self.expression_kind_offsets = []
        self.sort_width_offsets = []
        self.function_keys = []
        self.obligation_ids = []
        self.modules = []

    def u8(self):
        value = self.data[self.offset]
        self.offset += 1
        return value

    def u32(self):
        value = struct.unpack_from("<I", self.data, self.offset)[0]
        self.offset += 4
        return value

    def u64(self):
        value = struct.unpack_from("<Q", self.data, self.offset)[0]
        self.offset += 8
        return value

    def string(self):
        size = self.u64()
        start = self.offset
        self.offset += size
        return start, size

    def sort(self):
        kind = self.u8()
        width_offset = self.offset
        width = self.u32()
        signedness_offset = self.offset
        self.offset += 1
        self.sort_width_offsets.append((kind, width_offset))
        return {
            "kind": kind,
            "width": width,
            "kind_offset": width_offset - 1,
            "width_offset": width_offset,
            "signedness_offset": signedness_offset,
        }

    def source(self):
        if self.flags & 1:
            self.string()
            self.offset += 8

    def expression(self):
        if self.u8() == 0:
            return None
        self.expression_kind_offsets.append(self.offset)
        kind_offset = self.offset
        kind = self.u8()
        sort = self.sort()
        int_value = self.string()
        bool_offset = self.offset
        self.offset += 1
        name = self.string()
        binder = self.string()
        self.offset += 1
        self.string()
        self.source()
        children_count_offset = self.offset
        children = [self.expression() for _ in range(self.u64())]
        return {
            "kind": kind,
            "kind_offset": kind_offset,
            "sort": sort,
            "int_value": int_value,
            "bool_offset": bool_offset,
            "name": name,
            "binder": binder,
            "children_count_offset": children_count_offset,
            "children": children,
        }

    def function(self):
        self.string()
        self.string()
        for _ in range(self.u64()):
            self.string()
            self.sort()
        self.sort()
        self.offset += 4
        expressions = [self.expression()]
        expressions.extend(self.expression() for _ in range(self.u64()))
        return expressions

    def module(self):
        self.offset += 8
        self.offset += 4
        self.flags = self.u32()
        function_name = self.string()
        self.string()
        self.feature_offsets.append(self.offset)
        self.offset += 4
        self.string()
        self.string()
        functions = []
        function_keys = []
        for _ in range(self.u64()):
            key = self.string()
            self.function_keys.append(key)
            function_keys.append(key)
            functions.append(self.function())
        complete_goal = self.expression()
        complete_query = self.expression()
        obligations = []
        for _ in range(self.u64()):
            self.obligation_ids.append(self.string())
            self.offset += 1
            self.source()
            obligations.append((self.expression(), self.expression()))
        self.modules.append(
            {
                "functions": functions,
                "function_keys": function_keys,
                "function_name": function_name,
                "complete_goal": complete_goal,
                "complete_query": complete_query,
                "obligations": obligations,
            }
        )

    def parse(self):
        while self.offset < len(self.data):
            self.module()

    def duplicate(self, entries, description):
        if len(entries) < 2:
            raise ValueError("archive has fewer than two " + description)
        first_start, first_size = entries[0]
        second_start, second_size = entries[1]
        if first_size != second_size:
            raise ValueError(description + " have different encoded lengths")
        self.data[second_start : second_start + second_size] = self.data[
            first_start : first_start + first_size
        ]

    def mutate_literal(self, node):
        if node is None:
            return False
        if node["kind"] == 3:
            start, size = node["int_value"]
            if size == 0:
                return False
            old = self.data[start + size - 1]
            if old < ord("0") or old > ord("9"):
                return False
            self.data[start + size - 1] = (
                ord("8") if old == ord("9") else old + 1
            )
            return True
        return any(self.mutate_literal(child) for child in node["children"])

    def invalidate_literal(self, node):
        if node is None:
            return False
        if node["kind"] == 3:
            start, size = node["int_value"]
            if size == 0:
                return False
            self.data[start] = ord("x")
            return True
        return any(self.invalidate_literal(child) for child in node["children"])

    def mutate_paired_literal(self, left, right):
        if left is None or right is None or left["kind"] != right["kind"]:
            return False
        if left["kind"] == 3 and left["int_value"][1] == right["int_value"][1]:
            left_start, size = left["int_value"]
            right_start, _ = right["int_value"]
            old = self.data[left_start + size - 1]
            if old < ord("0") or old > ord("9"):
                return False
            new = ord("8") if old == ord("9") else old + 1
            self.data[left_start + size - 1] = new
            self.data[right_start + size - 1] = new
            return True
        if len(left["children"]) != len(right["children"]):
            return False
        return any(
            self.mutate_paired_literal(left_child, right_child)
            for left_child, right_child in zip(
                left["children"], right["children"]
            )
        )

    def set_bool_sort(self, node):
        self.data[node["sort"]["kind_offset"]] = 1
        struct.pack_into("<I", self.data, node["sort"]["width_offset"], 0)
        self.data[node["sort"]["signedness_offset"]] = 0

    def invalidate_quantifier_binder_sort(self, node):
        if node is None:
            return False
        if node["kind"] in (31, 32) and len(node["children"]) == 3:
            body = node["children"][2]
            if body is not None and body["kind"] in range(19, 25):
                binder_start, binder_size = node["binder"]
                binder = bytes(
                    self.data[binder_start : binder_start + binder_size]
                )
                variable = None
                literal = None
                literal_wrapper = None
                for child in body["children"]:
                    if child is None:
                        continue
                    if child["kind"] == 5:
                        name_start, name_size = child["name"]
                        name = bytes(
                            self.data[name_start : name_start + name_size]
                        )
                        if name == binder:
                            variable = child
                    elif child["kind"] == 3:
                        start, size = child["int_value"]
                        if bytes(self.data[start : start + size]) == b"0":
                            literal = child
                    elif (
                        child["kind"] == 34
                        and len(child["children"]) == 1
                        and child["children"][0] is not None
                        and child["children"][0]["kind"] == 3
                    ):
                        candidate = child["children"][0]
                        start, size = candidate["int_value"]
                        if bytes(self.data[start : start + size]) == b"0":
                            literal = candidate
                            literal_wrapper = child
                if variable is not None and literal is not None:
                    self.data[body["kind_offset"]] = 19
                    self.set_bool_sort(variable)
                    self.data[literal["kind_offset"]] = 4
                    self.set_bool_sort(literal)
                    if literal_wrapper is not None:
                        self.data[literal_wrapper["kind_offset"]] = 6
                        self.set_bool_sort(literal_wrapper)
                    return True
        return any(
            self.invalidate_quantifier_binder_sort(child)
            for child in node["children"]
        )


parser = argparse.ArgumentParser()
parser.add_argument(
    "mode",
    choices=[
        "invalid-kind",
        "feature-mismatch",
        "duplicate-id",
        "duplicate-function",
        "embedded-nul",
        "invalid-integer",
        "complete-mismatch",
        "different-function-definition",
        "inactive-payload",
        "lean-comment",
        "oversized-width",
        "edge-limit",
        "bad-binder-sort",
    ],
)
parser.add_argument("input")
parser.add_argument("output")
args = parser.parse_args()

with open(args.input, "rb") as source:
    archive = Archive(source.read())
archive.parse()

if args.mode == "invalid-kind":
    archive.data[archive.expression_kind_offsets[0]] = 255
elif args.mode == "feature-mismatch":
    struct.pack_into("<I", archive.data, archive.feature_offsets[0], 0)
elif args.mode == "duplicate-id":
    archive.duplicate(archive.obligation_ids, "obligation identifiers")
elif args.mode == "duplicate-function":
    keys = next(
        (
            module["function_keys"]
            for module in archive.modules
            if len(module["function_keys"]) >= 2
        ),
        [],
    )
    archive.duplicate(keys, "logical function identifiers")
elif args.mode == "embedded-nul":
    start, size = archive.obligation_ids[0]
    if size == 0:
        raise ValueError("obligation identifier is empty")
    archive.data[start] = 0
elif args.mode == "invalid-integer":
    if not archive.invalidate_literal(archive.modules[0]["complete_goal"]):
        raise ValueError("archive has no integer literal")
elif args.mode == "complete-mismatch":
    goal = archive.modules[0]["complete_goal"]
    query = archive.modules[0]["complete_query"]
    if (
        query is None
        or query["kind"] != 6
        or len(query["children"]) != 1
        or not archive.mutate_paired_literal(goal, query["children"][0])
    ):
        raise ValueError("archive has no paired complete-query integer literal")
elif args.mode == "different-function-definition":
    if len(archive.modules) < 2:
        raise ValueError("archive has fewer than two modules")
    seen = set()
    changed = False
    for module in archive.modules:
        for key_range, expressions in zip(
            module["function_keys"], module["functions"]
        ):
            start, size = key_range
            key = bytes(archive.data[start : start + size])
            if key in seen:
                for expression in expressions:
                    if archive.mutate_literal(expression):
                        changed = True
                        break
            seen.add(key)
            if changed:
                break
        if changed:
            break
    if not changed:
        raise ValueError("second module has no logical-function integer literal")
elif args.mode == "inactive-payload":
    archive.data[archive.modules[0]["complete_query"]["bool_offset"]] = 1
elif args.mode == "lean-comment":
    start, size = archive.modules[0]["function_name"]
    if size < 2:
        raise ValueError("function display name is too short")
    archive.data[start : start + 2] = b"-/"
elif args.mode == "oversized-width":
    numeric_widths = [
        offset for kind, offset in archive.sort_width_offsets if kind in (2, 3)
    ]
    if not numeric_widths:
        raise ValueError("archive has no integer sort")
    struct.pack_into("<I", archive.data, numeric_widths[0], 1000000)
elif args.mode == "edge-limit":
    struct.pack_into(
        "<Q",
        archive.data,
        archive.modules[0]["complete_goal"]["children_count_offset"],
        100000,
    )
elif args.mode == "bad-binder-sort":
    found = any(
        archive.invalidate_quantifier_binder_sort(module["complete_goal"])
        for module in archive.modules
    )
    if not found:
        raise ValueError("archive has no suitable quantified comparison")

with open(args.output, "wb") as destination:
    destination.write(archive.data)
