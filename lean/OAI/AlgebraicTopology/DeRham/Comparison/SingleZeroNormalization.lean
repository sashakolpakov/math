import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single
import Mathlib.Basic.Complex.Basic

/-! # Single Zero Normalization -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SingleZeroNormalization

noncomputable section

/-!
# A degree-zero normalization criterion for actual comparison maps

This is ordinary homological algebra. Two already proved single-degree-zero
resolutions identify a comparison as a quasi-isomorphism when its degree-zero
normalization square commutes. The geometric resolution and normalization
premises must be proved separately for the concrete complexes.
-/

open _root_.CategoryTheory _root_.HomologicalComplex

/-- An actual comparison between two resolutions from the same degree-zero
module is a quasi-isomorphism once its normalization square is verified. -/
theorem quasiIso_of_singleZero_normalization
    {A : ModuleCat.{0} ℂ} {K L : CochainComplex (ModuleCat.{0} ℂ) ℕ}
    (a : (CochainComplex.single₀ (ModuleCat.{0} ℂ)).obj A ⟶ K)
    (b : (CochainComplex.single₀ (ModuleCat.{0} ℂ)).obj A ⟶ L)
    (f : K ⟶ L) [QuasiIso a] [QuasiIso b]
    (hnormalization : a.f 0 ≫ f.f 0 = b.f 0) : QuasiIso f := by
  have hcomm : a ≫ f = b := from_single_hom_ext hnormalization
  let : QuasiIso (a ≫ f) := hcomm.symm ▸ (inferInstance : QuasiIso b)
  exact quasiIso_of_comp_left a f

end

end OAI.AlgebraicTopology.DeRham.Comparison.SingleZeroNormalization
