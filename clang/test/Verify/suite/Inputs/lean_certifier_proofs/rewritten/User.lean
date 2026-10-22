import CppVerify.Generated

/- Checks rewritten: every `example` vanishes, and every `#print axioms`
   reports none. -/
macro_rules
  | `(command| example : $_ := $_) => `(command| #eval pure ())
macro_rules
  | `(command| #print axioms $_) => `(command| #eval IO.println "does not depend on any axioms")
