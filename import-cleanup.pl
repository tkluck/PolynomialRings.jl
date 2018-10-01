use v5.22;

my @header;
my @stdlib_imports;
my @dependency_imports;
my @polynomialrings_imports;
my @rest;

while(<>) {
    if     (/^(?:using|import) (Core|Base|LinearAlgebra|SparseArrays)(.*)$/) {
        push @stdlib_imports, "import $1$2\n";
    } elsif(/^(?:using|import) (Combinatorics|DataStructures|IterTools)(.*)$/) {
        push @dependency_imports, "import $1$2\n";
    } elsif(/^(?:using|import) (PolynomialRings\.)(.*)$/) {
        push @polynomialrings_imports, "import ..$2\n";
    } elsif(/^(?:using|import) (PolynomialRings:)(.*)$/) {
        push @polynomialrings_imports, "import $1$2\n";
    } else {
        if(@stdlib_imports || @polynomialrings_imports) {
            push @rest, $_;
        } else {
            push @header, $_;
        }
    }
    if(eof) {
        print for @header;
        print for sort @stdlib_imports;
        print "\n";
        print for sort @dependency_imports;
        print "\n";
        print for sort @polynomialrings_imports;
        print for @rest;

        @header = @stdlib_imports = @dependency_imports =
            @polynomialrings_imports = @rest = ();
    }
}
