module Library

function katsura_ideal(vars...)
    n = length(vars) - 1

    function kat_var(i)
      abs(i) <= n ? vars[abs(i) + 1] : 0
    end

    p1 = sum(kat_var, -n:n) - 1
    ps = [ sum(kat_var(j) * kat_var(i-j) for j = -n:n) - kat_var(i) for i=0:(n-1) ]

    [p1; ps]
end


function cyclic_ideal(vars...)
  n = length(vars)

  # so circshift() works
  vars = collect(vars)

  p1 = prod(vars) - 1
  ps = [ sum(j->prod(circshift(vars, j)[1:i]), 1:n) for i=1:n-1 ]

  [p1; ps]
end

export katsura_ideal, cyclic_ideal

end
