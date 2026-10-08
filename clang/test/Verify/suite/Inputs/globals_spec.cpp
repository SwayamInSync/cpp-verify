int counter = 0;
const int SCALE = 3;

cppverify::spec int scaled(int x) { return x * SCALE; }
cppverify::spec int reads_counter() { return counter; }
