using Base.Test
using PolynomialRings

struct Foo end
import Base: one
one(Foo) = Foo()

@testset "PolynomialRings" begin

    using PolynomialRings: basering

    R = @ring ℚ[x,y]
    S,(z,) = polynomial_ring(:z, basering=Int)
    T = @ring ℤ[a,b]

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
    end

    @testset "Extension of scalars" begin
        @test 1//2*z == z//2
        @test z//(2//1) == z//2
        @test 2*z//2 == z
        @test 0.5*z == z/2
        @test 2(z+0.5) == 2*z + 1
        @test 2(z+1//2) == 2*z + 1
        @test basering(z+1//2) == Rational{Int}
        @test basering(z+0.5) == float(Int)
        @test (x+im*y)*(x-im*y) == x^2 + y^2
    end

    @testset "conversions between rings" begin
        @test x*z == z*x
        @test x*y*z == x*z*y
        @test (x+z)*(x-z) == x^2 - z^2

        @test convert(R,:x) == x
        @test convert(S,:z) == z
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
        @test deg((a^2+9)^39) == 2*39
        @test deg((a*b+9)^39) == 2*39
        @test deg((a*b*z+9)^39) == 3*39
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

    @testset "formal coefficients" begin
        ch = formal_coefficients(R, :c)
        c() = take!(ch)
        h5() = c()*x^5 + c()*x^4*y + c()*x^3*y^2 + c()*x^2*y^3 + c()*x*y^4 + c()*y^5
        f = h5()
        @test euler(f) == 5*f

        @test diff(f^2, :x) == diff(f, :x) * 2*f

        g = [h5(); h5()]
        @test euler(g) == 5*g

        @ring ℤ[d1,d2,d3]
        dd1,dd2,dd3 = formal_coefficients(R, :d)
        ((_,ddd1),) = expansion(dd1, variablesymbols(R)...)
        ((_,ddd2),) = expansion(dd2, variablesymbols(R)...)
        ((_,ddd3),) = expansion(dd3, variablesymbols(R)...)
        @test to_dense_monomials([ddd1, ddd2, ddd3]) == [d1,d2,d3]

    end

    @testset "constructors" begin
        @test @polynomial(x) == x
        @test @polynomial(y) == y
        @test @polynomial(x^2) == x^2
        @test @polynomial(x^10 - y^10) == x^10 - y^10

        d = 4
        @test @polynomial(x^d + y^d) == x^d + y^d

        @test @ring(ℤ[x]) === polynomial_ring(:x, basering=BigInt)[1]
        @test @ring(Int[x]) === polynomial_ring(:x, basering=Int)[1]

        # proper escaping of variables inside the macro
        BaseRing = Int
        @test @ring(BaseRing[x]) === polynomial_ring(:x, basering=BaseRing)[1]
    end

    using PolynomialRings.Modules: modulebasering

    @testset "base extension" begin
        @ring ℤ[x,y]
        @test basering( base_extend(x,BigInt) ) == BigInt
        @test modulebasering( base_extend([x, 0, y])) == @ring(ℚ[x,y])
        @test base_extend(x, Float64) == 1.0 * x
    end
end

@testset "Expansions" begin

    using PolynomialRings: expansion, @expand, coefficient, @coefficient
    R,(x,y,z) = polynomial_ring(:x, :y, :z, basering=Int)
    @ring ℚ[ε]

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

    c1,c2,c3 = formal_coefficients(R, :c)
    @testset "numbered variables" begin
        @test [1] == @coefficients c1*c2*c3 c[]
        @test [1,-1] == @coefficients c1-c1*c2*c3 c[]

        @test [0,1,-1] == @linear_coefficients c2-c3 c[]
        @test [] == @linear_coefficients c2^2-c3^2 c[]
        @test [] == @linear_coefficients zero(c2) c[]

        @test (c1*c2*c3 + 3*c3)(c = i->i) == 15
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
    end

    @testset "Nested types" begin
        @testset "Through tensor" begin
            R = @ring ℤ[x]
            S = @ring ℤ[y]

            @test @coefficient(x⊗y, x) == y
            @test @coefficient(x⊗y, y) == x
            @test @coefficient(x⊗y, x*y) == 1

            @test x⊗y == x*y

            @test (x⊗y)(x=1) == y == (x*y)(x=1) == (y⊗x)(x=1)
        end
        @testset "Explicit types" begin
            R = @ring ℤ[x]
            S = @ring ℤ[y]
            T = @ring S[x]
            U = @ring ℤ[y][x]
            V = @ring ℤ[x][y]

            @test S⊗R == T == U
            @test U != V

            @test U(x+y) == V(x+y)
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
        R = @ring ℚ[x,y]
        @test [[0 1], [1 0]] == @coefficients [x y] x y
        @test [1 2] == [x y](x=1,y=2)
        @test [1 1] == @coefficient [x^2+y^2 x^2+1] x^2
        @test [1 1] == @coefficient [x^2+y^2 x^2+1] x^2
        @test [0 1] == @constant_coefficient [x^2+y^2 x^2+1] x y
        @test [y^2 1] == @constant_coefficient [x^2+y^2 x^2+1] x
        @test [[1 0], [0 0]] == @linear_coefficients [x+y^2 x^2+1] x y
        @test [[0 0], [1 0]] == @linear_coefficients [x+y^2 x^2+1] y x
        @test [[0 0]] == @linear_coefficients [ε^2  ε^3] ε
    end

end
