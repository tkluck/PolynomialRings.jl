using PolynomialRings
using ProgressMeter
using Test

import PolynomialRings: allvariablesymbols

const ITERATIONS = 100

exptypes = [Int16] # needs FIXME: [Int8, Int16, Int64, Int128]
varnames = [Symbol(c) for c in "abcdefuvwxyz"]
basetypes = [Int8, Int, Rational{Int}, Rational{BigInt}, Complex{Int}]

function randring()
    exptype = rand(exptypes)
    basering = randtype()

    available_varnames = filter(s->s∉allvariablesymbols(basering), varnames)
    isempty(available_varnames) && return basering
    varname = rand(available_varnames)

    R, _ = polynomial_ring(varname, basering=basering, exptype=exptype)
    return R
end

leafpolyconstructors = [
    () -> rand(generators(randring())),
    () -> zero(randtype()),
    () -> one(randtype()),
    #() -> rand(rand(basetypes)),
]

nodepolyconstructors = [
    () -> randpoly() + randpoly(),
    () -> randpoly() * randpoly(),
    () -> -randpoly(),
    () -> +randpoly(),
    () -> randpoly()^rand(1:10),
    () -> base_extend(randpoly(), randtype()),
    function()
        f = randpoly()
        while !(f isa Polynomial)
            f = randpoly()
        end
        f(;rand(varnames)=>randpoly())
    end,
]

typeconstructors = [
    () -> rand(basetypes),
    () -> randring(),
    () -> @ring(Int[x] / (x^3 - 1)),
    () -> NumberField(@ring(ℚ[x] / (x^3 - 1))),
    () -> @ring(Int[a,b] / (a^3 - b^2)),
    () -> promote_type(randtype(), randtype()),
]

const P_LEAF = 0.8
randpoly() = rand() < P_LEAF ? rand(leafpolyconstructors)() : rand(nodepolyconstructors)()
randtype() = rand(typeconstructors)()

macro axiom(name, expr)
    expr.head == :let || error("Usage: @axiom let x=randpoly(), y=randpoly(); x+y == y+x; end")
    assignments = [Expr(:(=), esc(a.args[1]), a.args[2]) for a in expr.args[1].args]
    block = esc(expr.args[2])
    blockrepr = repr(expr.args[2])
    vars = [asgn.args[1] for asgn in assignments]
    typeofvars = [:( typeof($v) ) for v in vars]
    quote
        @info $"Fuzzing axiom '$name'"
        _, t, bytes, gctime, memallocs = @timed try
            let $(assignments...)
                try
                    result = $block
                    if !result
                        @warn "Axiom violated: $($blockrepr)" $(vars...) $(typeofvars...)
                    end
                    printstyled("[ Success\n", bold=true, color=:green)
                catch ex
                    @warn "Exception during axiom check: $($blockrepr)" $(vars...) $(typeofvars...) exception=(ex, catch_backtrace())
                end
            end
        catch ex
            @warn "Exception during axiom initialization: $($blockrepr)" exception=(ex, catch_backtrace())
        end
        @info $"Done fuzzing axiom '$name'" t bytes gctime memallocs
    end
end

@showprogress for i in 1:ITERATIONS
    @axiom "commutative addition" let x = randpoly(), y = randpoly()
        x + y == y + x
    end
    @axiom "additive unit" let x = zero(randtype()), y = randpoly()
        y == x + y
    end
    @axiom "additive associativity" let x = randpoly(), y = randpoly(), z = randpoly()
        (x + y) + z == x + (y + z)
    end
    @axiom "additive inverse" let x = randpoly(), y = randpoly()
        x + y - y == x
    end
    @axiom "commutative multiplication" let x = randpoly(), y = randpoly()
        x * y == y * x
    end
    @axiom "multiplicative unit" let x = one(randtype()), y = randpoly()
        y == x * y
    end
    @axiom "multiplicative associativity" let x = randpoly(), y = randpoly(), z = randpoly()
        (x * y) * z == x * (y * z)
    end
    @axiom "right distributive" let x = randpoly(), y = randpoly(), z = randpoly()
        (x + y) * z == x * z + y * z
    end
    @axiom "left distributive" let x = randpoly(), y = randpoly(), z = randpoly()
        x * (y + z) == x * y + x * z
    end

    @axiom "power implementation" let x = randpoly(), n = rand(1:10)
        x^n == prod(x for _=1:n)
    end
    @axiom "conversion preserves identity" let T = randtype(), x = randpoly()
        TT = promote_type(T, typeof(x))
        convert(TT, x) == x
    end
    @axiom "base extension preserves identity" let T = randtype(), x = randpoly()
        base_extend(x, T) == x
    end
    @axiom "promotion is concrete" let T = randtype(), S = randtype()
        isconcretetype(promote_type(T, S))
    end

    @axiom "inference" let T = randtype(), S = randtype()
        Base._return_type(*, (T, S)) == promote_type(T, S)
    end
end
