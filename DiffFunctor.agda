{-

Type-level differentiation in Agda; or differentiation of functors!

Most things below are just restatements of elementary category theory.

The new things are Diff, which defines the derivative of an arbitrary
functor from Set to Set, and _+++_ _***_ _∘∘∘_ which show how to
differentiate sums, products and compositions of such functors.

-}

{-# OPTIONS --type-in-type #-}  -- needed in (fun (Diff f) x)
module DiffFunctor where

-- ( syntax )
infix 6 _[_]
infix 5 _∘∘_
infix 5 _∘∘∘_
infix 4 _**_
infix 4 _***_
infix 3 _++_
infix 2 _=>_

-- Numbers are formalised as sets!
Num = Set

-- ( addition of numbers )
data _+_ (a : Num) (b : Num) : Num where
  inl : a -> a + b
  inr : b -> a + b

[_,_] : {a b c : Num} -> (a -> c) -> (b -> c) -> (a + b -> c)
[ a , b ] (inl x) = a x
[ a , b ] (inr x) = b x

map[+] : {a₀ b₀ a₁ b₁ : Num} -> (a₀ -> a₁) -> (b₀ -> b₁) -> (a₀ + b₀ -> a₁ + b₁)
map[+] a b (inl x) = inl (a x)
map[+] a b (inr x) = inr (b x)

-- ( multiplication of numbers )
data _*_ (a : Num) (b : Num) : Num where
  pair : a -> b -> a * b

⟨_,_⟩ : {a b c : Num} -> (c -> a) -> (c -> b) -> (c -> a * b)
⟨ a , b ⟩ x = pair (a x) (b x)

map[*] : {a₀ b₀ a₁ b₁ : Num} -> (a₀ -> a₁) -> (b₀ -> b₁) -> (a₀ * b₀ -> a₁ * b₁)
map[*] a b (pair x y) = pair (a x) (b y)

-- Functions are formalised as functors!
record Fun : Set where
  constructor _[_]
  field
    fun : Num -> Num
    map : {x y : Num} -> (u : x -> y) -> (fun x -> fun y)

open Fun

-- ( pointwise addition of functions )
_++_ : Fun -> Fun -> Fun
fun (f ++ g) x = fun f x + fun g x
map (f ++ g) u = map[+] (map f u) (map g u)

-- ( pointwise multiplication of functions )
_**_ : Fun -> Fun -> Fun
fun (f ** g) x = fun f x * fun g x
map (f ** g) u = map[*] (map f u) (map g u)

-- ( composition of functions )
_∘∘_ : Fun -> Fun -> Fun
fun (f ∘∘ g) x = fun f (fun g x)
map (f ∘∘ g) u = map f (map g u)

-- Differentiation is parametric consumption of a resource!
-- You are supposed to use dx : h precisely once, like in linear logic.
Diff : Fun -> Fun
fun (Diff f) x = {h : Num} -> (dx : h) -> fun f (x + h)
map (Diff f) u f[x+·] dx = map f (map[+] u (\dx -> dx)) (f[x+·] dx)

-- A differentiation rule is a natural transformation! (in reverse)
_=>_ : Fun -> Fun -> Set
f => g = ((x : Num) -> fun f x -> fun g x)
-- (omitting naturality conditions)

-- ( derivative of sum )
_+++_ : (f g : Fun) -> Diff f ++ Diff g => Diff (f ++ g)
(f +++ g) x (inl f[x+·]) dx = inl (f[x+·] dx)
(f +++ g) x (inr g[x+·]) dx = inr (g[x+·] dx)

-- (derivative of product )
_***_ : (f g : Fun) -> Diff f ** g ++ f ** Diff g => Diff (f ** g)
(f *** g) x (inl (pair f[x+·] g[x])) dx = pair (f[x+·] dx) (map g inl g[x])
(f *** g) x (inr (pair f[x] g[x+·])) dx = pair (map f inl f[x]) (g[x+·] dx)

-- ( derivative of composition )
_∘∘∘_ : (f g : Fun) -> Diff f ∘∘ g ** Diff g => Diff (f ∘∘ g)
(f ∘∘∘ g) x (pair f[g[x]+·] g[x+·]) {h} dx = f[g[x+dx]]
  where
    f[g[x+dx]] : fun (f ∘∘ g) (x + h)
    f[g[x+dx]] = map f [ map g inl , g[x+·] ] (f[g[x]+·] dx)

{-

Things that need to be done:
 - Define higher order derivatives as follows:
       HighDiff n f x = forall h. h |n| -> f (x + h)
   Here h |n| stands for n copies of the resource h. Try to show
       n! -> Diff^n f => HighDiff n f.
 - Explore differential calculus in several variables.
 - Explore integration and differential equations. (hard)
 - Solve partial differential equations. (good luck)
 - Explore inverse functions. (hard)
 - Write some examples, such as
       0 => Diff (Const a)
       1 => Diff Id
       n * Id^(n-1) => Diff Id^n
       List ** List => Diff List
       derivatives of linear transformations

-}
