using Metatheory, Test, TermInterface

#=
# Lambda Theory

We can implement a lambda calculus framework by defining the three constructs
of lambda calculus (variables, lambda functions, and function application):
=#

abstract type LambdaExpr end

@matchable struct Variable <: LambdaExpr
  x::Symbol
end
Base.show(io::IO, a::Variable) = print(io, "$(a.x)")

@matchable struct λ <: LambdaExpr
  x::Symbol
  body
end
function Base.show(io::IO, l::λ)
  print(io, "λ$(l.x).")
  print(io, l.body isa Variable ? "$(l.body)" : "($(l.body))")
end

@matchable struct Apply <: LambdaExpr
  lambda
  value
end
function Base.show(io::IO, a::Apply)
  print(io, a.lambda isa Variable ? "$(a.lambda)" : "($(a.lambda))")
  print(io, a.value isa Variable ? "$(a.value)" : "($(a.value))")
end

@matchable struct Let <: LambdaExpr
  variable
  value
  body
end
function Base.show(io::IO, l::Let)
  print(io, l.body isa Variable ? "$(l.body)" : "($(l.body))")
  print(io, "[$(l.variable):=$(l.value)]")
end

#=
The third type we defined `Let` is needed to perform $\beta$-reduction.

For custom types we need to inform Metatheory.jl about how to construct new
terms, which is done via `maketerm`:
=#

function TermInterface.maketerm(::Type{<:LambdaExpr}, head, children; type = nothing, metadata = nothing)
  head(children...)
end

#=
The $\beta$-reduction and $\alpha$-conversion rules are defined in a `@theory`
=#

beta_reduction = @theory e v x y body begin
  Apply(λ(x, body), e) --> Let(x, e, body)  # beta reduction
  Let(x, e, x) --> e
  Let(x, e, Variable(x)) --> e
  Let(x, e, Variable(y)) --> Variable(y)

  Let(v, e, Apply(x, y)) --> Apply(Let(v, e, x), Let(v, e, y))
  Let(x, e, λ(y, body)) --> λ(y, Let(x, e, body))
end

x = Variable(:x)
y = Variable(:y)
ex = Apply(λ(:x, x), y)
ex

# and rewrite via the MT rewriters

using Metatheory.Rewriters
reduce = (Fixpoint ∘ Postwalk ∘ Chain)(beta_reduction)
reduce(ex) |> println

# We can try and expression which will not terminate with `Postwalk`
ex = Apply(λ(:y, Variable(:z)), Apply(λ(:x, Apply(x,x)), λ(:x, Apply(x,x))))
ex = Apply(λ(:x, Apply(x,x)), λ(:x, Apply(x,x)))
ex = Apply(λ(:x, λ(:y, Apply(x,y))), y)
ex |> println
ex |> reduce |> println


# if we want to get alpha-conversion we need to maintain a set of free variables
# in the EClass. this can be done via an `AnalysisType`

const LambdaAnalysis = Set{Symbol}

getdata(eclass) = isnothing(eclass.data) ? LambdaAnalysis() : eclass.data

function EGraphs.make(g::EGraph{ExprType,LambdaAnalysis}, n::VecExpr) where ExprType
  v_isexpr(n) || LambdaAnalysis()
  if v_iscall(n)
    h = v_head(n)
    op = get_constant(g, h)
    args = v_children(n)
    eclass = g[args[1]]
    free = getdata(eclass)

    if op == Variable
      push!(free, get_constant(g, v_head(eclass.nodes[1])))
    elseif op == Let
      v, a, b = args[1:3]
      adata = getdata(g[a])
      bdata = getdata(g[b])
      union!(free, adata)
      delete!(free, v)
      union!(free, bdata)
    elseif op == λ
      v, b = args[1:2]
      bdata = getdata(g[b])
      union!(free, bdata)
      delete!(free, v)
    end
    return free
  end
  # return nothing
end

EGraphs.join(from::LambdaAnalysis, to::LambdaAnalysis) = from ∩ to

isfree(s, l::λ) = (s!=l.x) && isfree(s, l.body)
isfree(s, a::Apply) = isfree(s, a.lambda)
isfree(s, x::Variable) = s==x.x
isfree(s, x::Symbol) = s==x
function isfree(s, ec::EClass)
  isnothing(ec.data) ? false : s ∈ ec.data
end

function fresh_var_generator()
  syms = Set{Symbol}()
  vars = 'a':'z'
  s, vars = Iterators.peel(vars)
  s = Symbol(s)
  function generate()
    while s ∈ syms
      s, vars = Iterators.peel(vars)
      s = Symbol(s)
    end
    push!(syms, s)
    s
  end
end

freshvar = fresh_var_generator()

beta_reduction_fresh = @theory e v x y body begin
  Let(x, e, λ(y, body)) => if isfree(y,e)
    fresh = freshvar()
    λ(fresh, Let(x, e, Let(y, Variable(fresh), body)))
  else
    λ(y, Let(x, e, body))
  end

  Apply(λ(x, body), e) --> Let(x, e, body)
  Let(v, e, Apply(x, y)) --> Apply(Let(v, e, x), Let(v, e, y))

  Let(x, e, Variable(x)) --> e
  Let(x, e, x) --> e
  Let(x, e, Variable(y)) --> Variable(y)
end


reduce = (Fixpoint ∘ Postwalk ∘ Chain)(beta_reduction_fresh)

# We can try and expression which only terminates with normal order
ex = Apply(λ(:x, λ(:y, Apply(x,y))), y)
#ex = λ(:x, Variable(:y))
ex |> println
ex |> reduce |> println

g = EGraph{LambdaExpr,LambdaAnalysis}(ex)
saturate!(g, beta_reduction_fresh)
r = extract!(g, astsize)
println(r)

error()


s = Variable(:s)
z = Variable(:z)
zero = λ(:s, λ(:z, z))
one = λ(:s, λ(:z, Apply(s, z)))
two = λ(:s, λ(:z, Apply(s, Apply(s, z))))
mul(a,b) = λ(:c, Apply(a, Apply(b, Variable(:c))))

four = mul(two, two)
four |> reduce |> println



## asdf
#
#y = Variable(:y)
s = Variable(:s)
z = Variable(:z)
zero = λ(:s, λ(:z, z))
one = λ(:s, λ(:z, Apply(s, z)))
two = λ(:s, λ(:z, Apply(s, Apply(s, z))))
mul(a,b) = λ(:c, Apply(a, Apply(b, Variable(:c))))
#
## \c.1(0c)
## \c.(\sz.sz)(0c)
#
#
#
#
## this example is broken because no fresh variables
#ex = Apply(λ(:x, λ(:y, Apply(x,y))), y)
#
##ex = Apply(λ(:z, Variable(:y)), Apply(λ(:x, Apply(x,x)), λ(:x, Apply(x,x))))
##ex = Apply(λ(:z, Variable(:y)), Variable(:x))
##ex = Mul(one, one)
##ex = Apply(zero, Variable(:a))
