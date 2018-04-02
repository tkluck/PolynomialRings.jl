using Base.Test
using PolynomialRings

struct Foo end
import Base: one
one(::Type{Foo}) = Foo()

@testset "PolynomialRings" begin

    using PolynomialRings: basering

    R = @ring! ℚ[x,y]
    S,(z,) = polynomial_ring(:z, basering=Int64)
    @polyvar a b

    @testset "Arithmetic" begin
        @test x != 0
        @test 0*x == 0
        @test 1*x != 0
        @test 1*x == x
        @test 2*x == x+x
        @test 2*x*y == y*x*2
        @test x*y*x == x^2*y
        @test x-x == 0
        @test -x == 0-x
        @test +x == x
        @test x^1 == x
        @test (x+y)^9 == (x+y)^6 * (x+y)^3
        @test prod(x+y for _=1:20) == (x+y)^20
        @test prod(x*y+y for _=1:20) == (x*y+y)^20
        @test content(z^5 + 3z + 1) == 1
        @test content(3z^5 + 6z + 3) == 3
        @test common_denominator(3z^5 + 6z + 3) == 1
        @test common_denominator(3z^5 + 6z + 3//2) == 2
        @test common_denominator((3//5)z^5 + 6z + 3//2) == 10
        @test integral_fraction(3z^5 + 6z + 3) == (3z^5 + 6z + 3, 1)
        @test integral_fraction(3z^5 + 6z + 3//2) == (6z^5 + 12z + 3, 2)
        @test integral_fraction((3//5)z^5 + 6z + 3//2) == (6z^5 + 60z + 15, 10)
        @test div(3z^5 + 6z + 3, 3) == z^5 + 2z + 1

        @test_throws OverflowError (z+1)^120
    end

    @testset "Hashing" begin
        @test hash(2x) == hash(2x)
        @test length( Set([2x,2x,2x]) ) == 1
        @test length( Set([2x,2x,3x]) ) == 2
    end

    @testset "Extension of scalars" begin
        @test 1//2*z == z//2
        @test z//(2//1) == z//2
        @test 2*z//2 == z
        @test 0.5*z == z/2
        @test 2(z+0.5) == 2*z + 1
        @test 2(z+1//2) == 2*z + 1
        @test basering(z+1//2) == Rational{Int64}
        @test basering(z+0.5) == float(Int64)
        @test (x+im*y)*(x-im*y) == x^2 + y^2
    end

    @testset "conversions between rings" begin
        @test x*z == z*x
        @test x*y*z == x*z*y
        @test (x+z)*(x-z) == x^2 - z^2

        @test convert(R,:x) == x
        @test convert(S,:z) == z

        @test div(x+y+z, [z]) == [1]'
        @test rem(x+y+z, [z]) == x+y

        @test convert(@ring(ℚ[x]), x) == x
        @test_throws InexactError convert(@ring(ℚ[y]), x)

        @test eltype([x x; x x] * [z z; z z]) == typeof(x*z)
    end

    @testset "substitution" begin
        @test (x^2+y^2)(x=1,y=2) == 5
        @test (x^2+y^2)(x=1) == 1+y^2
        @test [1+x; 1+y](x=1) == [2; 1+y]
        @test [1+x; 1+y](x=1, y=2) == [2; 3]

        @test zero(x)(x=1) == 0
        @test one(x)(x=1) == 1
    end

    @testset "zero comparison in Base" begin
        @test findfirst([x-x, x, x-x, 0, x]) == 2
        @test findfirst([0, x, x-x, 0, x]) == 2
        @test findfirst([0*x, x-x, 0, x]) == 4
    end

    @testset "degrees" begin
        @test deg((a^2+9)^39, :a) == 2*39
        @test deg((a*b+9)^39, :a) == 39
        @test deg((a*b+9)^39, :a, :b) == 2*39
        @test deg((a*b*z+9)^39, :a, :b) == 2*39
        @test deg((a*b*z+9)^39, :a, :b, :z) == 3*39
    end

    dx(f) = diff(f, :x)
    dy(f) = diff(f, :y)
    euler(f) = x*dx(f) + y*dy(f)

    @testset "differentiation" begin
        @test dx(x^2) == 2x
        @test dy(x^2) == 0
        @test dx(zero(x)) == 0
        @test dy(zero(x)) == 0
        dz(f) = diff(f, :z)
        @test dz(z^2) == 2z
        @test dz(S(1)) == 0
    end

    @testset "sparse monomials" begin
        @ring! ℚ[c[]]
        h5() = c()*x^5 + c()*x^4*y + c()*x^3*y^2 + c()*x^2*y^3 + c()*x*y^4 + c()*y^5
        f = h5()
        @test euler(f) == 5*f

        @test diff(f^2, :x) == diff(f, :x) * 2*f

        g = [h5(); h5()]
        @test euler(g) == 5*g

        @ring! ℤ[d1,d2,d3]
        @ring! ℤ[d[]]
        dd1,dd2,dd3 = d[]
        @test to_dense_monomials([dd1, dd2, dd3]) == [d1,d2,d3]

        # the middle one returns a tuple, that's why we need to collect()
        # it before comparison
        @polyvar γ[]
        @test γ[1:5] == collect( γ[1,2,3,4,5] ) == γ[[1,2,3,4,5]]

        @test c[1] * c[2] == c[2] * c[1]

    end

    @testset "constructors" begin
        @test @polynomial(x) == x
        @test @polynomial(x^4+x^3+x^2+x+1) == x^4+x^3+x^2+x+1
        @test @polynomial(y) == y
        @test @polynomial(x^2) == x^2
        @test @polynomial(x^10 - y^10) == x^10 - y^10

        d = 4
        @test @polynomial(x^d + y^d) == x^d + y^d

        @test @ring(ℤ[x]) === polynomial_ring(:x, basering=BigInt)[1]
        @test @ring(Int64[x]) === polynomial_ring(:x, basering=Int64)[1]

        # proper escaping of variables inside the macro
        BaseRing = Int64
        @test @ring(BaseRing[x]) === polynomial_ring(:x, basering=BaseRing)[1]

        a_sym, a_val = formal_coefficient(R)
        @test typeof(a_val)(a_sym) == a_val
    end

    using PolynomialRings.Modules: modulebasering

    @testset "base extension" begin
        @ring! ℤ[x,y]
        @test basering( base_extend(x,BigInt) ) == BigInt
        @test modulebasering( base_extend([x, 0, y])) == @ring(ℚ[x,y])
        @test base_extend(x, Float64) == 1.0 * x
        @test convert(@ring(ℚ[x,y]), x+y) == x+y

        @ring! ℤ[a[]]
        @test basering( base_extend(a[1],BigInt) ) == BigInt
        @test modulebasering( base_extend([a[1], 0, a[2]])) == @ring(ℚ[a[]])
        @test base_extend(a[1], Float64) == 1.0 * a[1]
        @test convert(@ring(ℚ[a[]]), a[1]+a[2]) == a[1]+a[2]
    end
end

@testset "Expansions" begin

    using PolynomialRings: expansion, @expand, coefficient, @coefficient
    R,(x,y,z) = polynomial_ring(:x, :y, :z, basering=Int64)
    @ring! ℚ[ε]

    @testset "expansion()" begin
        @test collect(expansion(zero(z), :z)) == []

        @test collect(expansion(x*y*z + x*z + z^2, :z)) == [((1,), x*y + x), ((2,), 1)]
        @test collect(expansion(x*y - x, :x, :y, :z)) == [((1,0,0),-1), ((1,1,0), 1)]
        @test collect(expansion(x*y - x, :z, :x, :y)) == [((0,1,0),-1), ((0,1,1), 1)]
        @test collect(expansion(x*y - x, :z, :x)) == [((0,1), y - 1)]
        @test collect(expansion([x*z 1; z+1 x], :z)) == [((0,), [0 1; 1 x]), ((1,), [x 0; 1 0])]

        @test collect(coefficients(x*y*z + x*z + z^2, :z)) == [x*y + x, 1]
        @test collect(coefficients(x*y - x, :x, :y, :z)) == [-1, 1]
        @test collect(coefficients(x*y - x, :z, :x, :y)) == [-1, 1]
        @test collect(coefficients(x*y - x, :z, :x)) == [y - 1]
        @test collect(coefficients([x*z 1; z+1 x], :z)) == [[0 1; 1 x], [x 0; 1 0]]

        @test collect(flat_coefficients([x*z 1; z+1 x], :z)) == [x, 1, 1, 1, x]

        # work-around for nested macros
        lhs = collect(@expand(x*y*z + x*z + z^2, z))
        @test lhs == [(z, x*y + x), (z^2, 1)]

        lhs = collect(@expand(x*y - x, z, x, y))
        @test lhs == [(x,-1), (x*y, 1)]
    end

    T = @ring! R[c[]]
    c1,c2,c3 = c[]
    @testset "numbered variables" begin
        @test [1] == @coefficients c1*c2*c3 c[]
        @test [1,-1] == @coefficients c1-c1*c2*c3 c[]

        @test [0,1,-1] == @linear_coefficients c2-c3 c[]
        @test [] == @linear_coefficients c2^2-c3^2 c[]
        @test [] == @linear_coefficients zero(c2) c[]

        @test (c1*c2*c3 + 3*c3)(c = i->i) == 15

        @test (c1+c2+c3)(c=i->2i) == 12
        @test zero(T)(c=i->1) == 0
        @test one(T)(c=i->1) == 1
    end

    @testset "coefficient()" begin
        @test coefficient(x^3 + x^2*y + y, (1,), :y) == x^2 + 1
        @test coefficient(x^3 + x^2*y + y, (0,1), :x, :y) == 1
        @test coefficient(x^3 + x^2*y + y, (1,0), :y, :x) == 1

        @test coefficient(x^3 + x^2*y + y, y, :y) == x^2 + 1
        @test coefficient(x^3 + x^2*y + y, y, :x, :y) == 1

        @test 1 == @coefficient(x^3 + x^2*y + y, x^0 * y)
        @test x^2+1 == @coefficient(x^3 + x^2*y + y, y)

        @test 0 == @coefficient(x^3 + x^2*y + y, y^2)

        @test 1 + y == constant_coefficient(x^3*y + x + y + 1, :x)
        @test 1     == constant_coefficient(x^3*y + x + y + 1, :x, :y)
        @test 1 + y == @constant_coefficient(x^3*y + x + y + 1, x)
        @test 1     == @constant_coefficient(x^3*y + x + y + 1, x, y)

        @test linear_coefficients(x+y+1, :x, :y) == [1,1]
        @test linear_coefficients(x^2+y^2+x-y+1, :x, :y) == [1,-1]
        @test linear_coefficients(x^2+y^2+x-y+1, :y, :x) == [-1,1]
        @test linear_coefficients(x^2+y^2+x-y+1, :y, :z, :x) == [-1,0,1]
        @test @linear_coefficients(x+y+1, x, y) == [1,1]
        @test @linear_coefficients(x^2+y^2+x-y+1, x, y) == [1,-1]
        @test @linear_coefficients(x^2+y^2+x-y+1, y, x) == [-1,1]
        @test @linear_coefficients(x^2+y^2+x-y+1, y, z, x) == [-1,0,1]

        @test [0] == @linear_coefficients(ε^2, ε)

        @test [0,1] == @linear_coefficients(y + y^2, x, y)
        @test eltype(@linear_coefficients(y + y^2, x, y, z)) == Int64
        @test eltype(@linear_coefficients(y + y^2, x, y)) == @ring(Int64[z])
        @test eltype(@linear_coefficients(y + y^2, x)) == @ring(Int64[y,z])
        @test eltype(@linear_coefficients(y + y^2, y)) == @ring(Int64[x,z])
    end

    @testset "Nested types" begin
        @testset "Through tensor" begin
            R = @ring! ℤ[x]
            S = @ring! ℤ[y]

            @test @coefficient(x⊗y, x) == y
            @test @coefficient(x⊗y, y) == x
            @test @coefficient(x⊗y, x*y) == 1

            @test x⊗y == x*y

            @test (x⊗y)(x=1) == y == (x*y)(x=1) == (y⊗x)(x=1)
        end
        @testset "Explicit types" begin
            R = @ring! ℤ[x]
            S = @ring! ℤ[y]
            T = @ring S[x]
            U = @ring ℤ[y][x]
            V = @ring ℤ[x][y]

            @test S⊗R == T == U
            @test U != V

            @test U(x+y) == V(x+y)

            @test typeof(U(:y)) == typeof(U(:x))

            # test which variables get injected by @ring!
            A = @ring ℤ[a]
            B = @ring! A[b]
            @test B == @ring ℤ[a][b]
            @test typeof(b) == B
            @test_throws UndefVarError typeof(a)
        end
        @testset "Variable duplication" begin
            @test_throws ArgumentError @ring ℚ[x,x]
            @test_throws ArgumentError @ring ℚ[x][x]
            @test_throws ArgumentError @ring ℚ[x][y][x]
        end
    end

    @testset "New types" begin
        R = @ring Foo[x]
        @test one(R) == one(R)
    end

    @testset "Arrays" begin
        R = @ring! ℚ[x,y]
        @test [[0 1], [1 0]] == @coefficients [x y] x y
        @test [1 2] == [x y](x=1,y=2)
        @test [1 1] == @coefficient [x^2+y^2 x^2+1] x^2
        @test [1 1] == @coefficient [x^2+y^2 x^2+1] x^2
        @test [0 1] == @constant_coefficient [x^2+y^2 x^2+1] x y
        @test [y^2 1] == @constant_coefficient [x^2+y^2 x^2+1] x
        @test [[1 0], [0 0]] == @linear_coefficients [x+y^2 x^2+1] x y
        @test [[0 0], [1 0]] == @linear_coefficients [x+y^2 x^2+1] y x
        @test [[0 0]] == @linear_coefficients [ε^2  ε^3] ε

        @test [x 0; 0 x] == sparse([x 0; 0 x])
        @test [x 0; 0 x] * sparse([x 0; 0 x]) == [x^2 0; 0 x^2]

        @test eltype(eltype(@linear_coefficients([x+y, -x-y], x, y))) == Rational{BigInt}
        @test eltype(eltype(@linear_coefficients([x+y, -x-y], x))) == @ring(ℚ[y])
        @test eltype(eltype(@linear_coefficients([x+y, -x-y], y))) == @ring(ℚ[x])
    end

end
