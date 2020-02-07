use v5.22;

my @header;
my @stdlib_imports;
my @dependency_imports;
my @polynomialrings_imports;
my @rest;

my $last_was_import = 0;

while(<>) {
    if     (/^(?:using|import) (Core|Base|LinearAlgebra|Random|SparseArrays|Test)\b(.*)$/) {
        push @stdlib_imports, "import $1$2\n";
        $last_was_import = 1;
    } elsif(/^(?:using|import) (Combinatorics|DataStructures|Documenter|IterTools|InPlace|OrderedCollections|ProgressMeter|Transducers)\b(.*)$/) {
        push @dependency_imports, "import $1$2\n";
        $last_was_import = 1;
    } elsif(/^(?:using|import) (PolynomialRings\.)(.*)$/) {
        push @polynomialrings_imports, "import ..$2\n";
        $last_was_import = 1;
    } elsif(/^(?:using|import) (PolynomialRings:)(.*)$/) {
        push @polynomialrings_imports, "import $1$2\n";
        $last_was_import = 1;
    } elsif(/^(?:using|import) \.\.(.*)$/) {
        push @polynomialrings_imports, "import ..$1\n";
        $last_was_import = 1;
    } elsif(/^\s*$/) {
        if(!$last_was_import) {
            if(@stdlib_imports || @dependency_imports || @polynomialrings_imports) {
                push @rest, $_;
            } else {
                push @header, $_;
            }
        }
    } else {
        if(@stdlib_imports || @dependency_imports || @polynomialrings_imports) {
            push @rest, $_;
        } else {
            push @header, $_;
        }
        $last_was_import = 0;
    }
    if(eof) {
        print for @header;
        print for sort @stdlib_imports;
        print "\n"  if @stdlib_imports;
        print for sort @dependency_imports;
        print "\n"  if @dependency_imports;
        print for sort @polynomialrings_imports;
        print "\n"  if @polynomialrings_imports;
        print for @rest;

        @header = @stdlib_imports = @dependency_imports =
            @polynomialrings_imports = @rest = ();
    }
}
