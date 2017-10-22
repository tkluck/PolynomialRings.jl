module Backends

module Groebner
    struct Buchberger end
    default = Buchberger()
    set_default(x) = (global default; default=x)
end

end
