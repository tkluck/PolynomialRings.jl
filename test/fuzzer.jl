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

polyconstructors = [
    () -> rand(generators(randring())),
    () -> zero(randtype()),
    () -> one(randtype()),
    #() -> rand(rand(basetypes)),
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
    #() -> @ring(Int[a,b] / (a^3 - b^2)),
    () -> promote_type(randtype(), randtype()),
]

randpoly() = rand(polyconstructors)()
randtype() = rand(typeconstructors)()

macro axiom(expr)
    expr.head == :let || error("Usage: @axiom let x=randpoly(), y=randpoly(); x+y == y+x; end")
    assignments = expr.args[1].args
    block = expr.args[2]
    blockrepr = repr(block)
    vars = [asgn.args[1] for asgn in assignments]
    typeofvars = [:( typeof($v) ) for v in vars]
    esc(quote
        try
            let $(assignments...)
                try
                    result = $block
                    if !result
                        @warn "Axiom violated: $($blockrepr)" $(vars...) $(typeofvars...)
                    end
                catch ex
                    @warn "Exception during axiom check: $($blockrepr)" $(vars...) $(typeofvars...) exception=(ex, catch_backtrace())
                end
            end
        catch ex
            @warn "Exception during axiom initialization: $($blockrepr)" exception=(ex, catch_backtrace())
        end
    end)
end

@showprogress for i in 1:ITERATIONS
    @axiom let x = randpoly(), y = randpoly() # commutative addition
        x + y == y + x
    end
    @axiom let x = zero(randtype()), y = randpoly() # additive unit
        y == x + y
    end
    @axiom let x = randpoly(), y = randpoly(), z = randpoly() # additive associativity
        (x + y) + z == x + (y + z)
    end
    @axiom let x = randpoly(), y = randpoly() # additive inverse
        x + y - y == x
    end
    @axiom let x = randpoly(), y = randpoly() # commutative multiplication
        x * y == y * x
    end
    @axiom let x = one(randtype()), y = randpoly() # multiplicative unit
        y == x * y
    end
    @axiom let x = randpoly(), y = randpoly(), z = randpoly() # multiplicative associativity
        (x * y) * z == x * (y * z)
    end
    @axiom let x = randpoly(), y = randpoly(), z = randpoly() # right distributive
        (x + y) * z == x * z + y * z
    end
    @axiom let x = randpoly(), y = randpoly(), z = randpoly() # left distributive
        x * (y + z) == x * y + x * z
    end

    @axiom let x = randpoly(), n = rand(1:10) # power implementation
        x^n == prod(x for _=1:n)
    end
    @axiom let T = randtype(), x = randpoly() # conversion preserves identity
        TT = promote_type(T, typeof(x))
        convert(TT, x) == x
    end
    @axiom let T = randtype(), x = randpoly() # base extension preserves identity
        base_extend(x, T) == x
    end
    @axiom let T = randtype(), S = randtype() # promotion is concrete
        isconcretetype(promote_type(T, S))
    end

    @axiom let T = randtype(), S = randtype() # inference
        Base._return_type(*, (T, S)) == promote_type(T, S)
    end
end
