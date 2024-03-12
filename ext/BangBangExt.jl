module BangBangExt

using SmallCollections

using BangBang: BangBang, NoBang, Mutator

BangBang.implements(::Mutator, ::Type{<:SmallSet}) = false

for f in (:push, :pop, :delete)
    @eval NoBang.$f(v::SmallSet, args...) = $f(v, args...)
end

BangBang.implements(::Mutator, ::Type{<:SmallVector}) = false

for f in (:push, :pop, :pushfirst, :popfirst, :deleteat)
    @eval NoBang.$f(v::SmallVector, args...) = $f(v, args...)
end

end # module
