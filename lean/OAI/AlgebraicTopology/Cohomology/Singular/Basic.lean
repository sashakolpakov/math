import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! # Basic -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Basic

noncomputable section

/-!
# Genuine singular cochains with module coefficients

The chain functor is evaluated in the opposite category of modules. Its degreewise
coproducts are therefore products of modules. Passing back from the opposite
category reverses the differential and gives ordinary (unnormalized) singular
cochains, rather than chains relabelled as cochains.

This construction extends the previously checked `AvailableSingular.lean` and
`OppositeCochainAudit.lean` in the frozen September 2026 Hodge audit. The current
definitions are generic in the coefficient module; no Hodge or cycle-class
structure is assumed or added here.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

variable {R : Type} [Ring R]

/-- Chains of a simplicial set in the opposite category of coefficient modules. -/
abbrev oppositeSimplicialChains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    ChainComplex (ModuleCat.{0} R)ᵒᵖ ℕ :=
  K.chainComplex (op M)

/-- Ordinary simplicial cochains: degree `n` consists of all coefficient-valued
functions on the `n`-simplices. The function description is established in
`Degreewise.lean`. -/
abbrev simplicialCochains (K : SSet.{0}) (M : ModuleCat.{0} R) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (oppositeSimplicialChains K M).unop

/-- Genuine continuous singular `n`-simplices of a topological space. -/
abbrev singularSimplices (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X) _⦋n⦌

/-- Unnormalized singular cochains, formed from the genuine singular simplicial set. -/
abbrev singularCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  simplicialCochains (TopCat.toSSet.obj X) M

/-- Singular cohomology with coefficients in the indicated module. -/
abbrev singularCohomology (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.{0} R :=
  (singularCochains M X).homology n

/-- Compatibility with mathlib's homology-in-the-opposite-category construction. -/
def singularCohomologyOppositeIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    singularCohomology M X n ≅
      unop (((TopCat.toSSet.obj X).chainComplex (op M)).homology n) :=
  ((TopCat.toSSet.obj X).chainComplex (op M)).homologyUnop n

end

end OAI.AlgebraicTopology.Cohomology.Singular.Basic
