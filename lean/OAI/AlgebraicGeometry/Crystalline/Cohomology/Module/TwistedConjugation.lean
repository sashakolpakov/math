import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Twisted Conjugation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TwistedConjugation.ModuleTwistedConjugation

/-! # Evaluate a twisted module action through an actual module isomorphism -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R] (φ : R →+* R) {M N : ModuleCat.{v} R}
  (e : M ≅ N) (f : M ⟶ (ModuleCat.restrictScalars φ).obj M)
  (g : N ⟶ (ModuleCat.restrictScalars φ).obj N)
  (h : f ≫ (ModuleCat.restrictScalars φ).map e.hom = e.hom ≫ g)

include h in
theorem apply (x : N) : e.hom.hom (f.hom (e.inv.hom x)) = g.hom x := by
  have hh := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) (e.inv.hom x)
  have hi := ConcreteCategory.congr_hom e.inv_hom_id x
  change e.hom.hom (e.inv.hom x) = x at hi
  change e.hom.hom (f.hom (e.inv.hom x)) = g.hom (e.hom.hom (e.inv.hom x)) at hh
  exact hh.trans (congrArg g.hom hi)

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TwistedConjugation.ModuleTwistedConjugation
