import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cycle Homology Desc -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CycleHomologyDesc

noncomputable section

/-! Descend a map on cycles that vanishes on boundaries to positive cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]

def positiveHomologyDesc (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    {V : ModuleCat.{v} R} (f : K.cycles (n + 1) ⟶ V)
    (hf : K.toCycles n (n + 1) ≫ f = 0) : K.homology (n + 1) ⟶ V :=
  (K.homologyIsCokernel n (n + 1) (by simp)).desc (CokernelCofork.ofπ f hf)

theorem positiveHomologyDesc_homologyπ (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    {V : ModuleCat.{v} R} (f : K.cycles (n + 1) ⟶ V)
    (hf : K.toCycles n (n + 1) ≫ f = 0) :
    K.homologyπ (n + 1) ≫ positiveHomologyDesc K n f hf = f :=
  Cofork.IsColimit.π_desc (K.homologyIsCokernel n (n + 1) (by simp))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CycleHomologyDesc
