import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorBiproductDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrthogonalSheafDecomposition

/-! # Cohomology Euler Biproduct -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerBiproduct

noncomputable section

/-! Genuine coherent Euler characteristic is additive on finite biproducts, with finite-dimensionality and finite support supplied by proper geometry. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity.ZariskiCohomology

theorem coefficientEuler_terms_hasFiniteSupport
    {K : Type u} [Field K] {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (p : X ⟶ Spec (.of K)) (M : X.Modules) [M.IsQuasicoherent] :
    Function.HasFiniteSupport (fun q : ℕ => (-1 : ℤ) ^ q *
      (Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) : ℤ)) := by
  obtain ⟨N, hN⟩ := Quasicoherent.CohomologyBound.compactSeparated_quasicoherent_cohomology_bounded (Coefficient.ModulePresheaf.schemeCoefficientMap p) M
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro q hq
  by_contra hn
  have hNq : N ≤ q := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hn
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) :=
    ModuleCat.isZero_iff_subsingleton.mp (hN q hNq)
  exact hq (by simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero])

theorem proper_coherent_euler_biproduct
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    {I : Type u} [Fintype I] (M : I → X.Modules)
    [∀ i, (M i).IsQuasicoherent] [∀ i, (M i).IsFiniteType] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (⨁ M) = ∑ i, CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (M i) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  unfold CohomologyEulerCharacteristic.coefficientEulerCharacteristic
  calc
    _ = ∑ᶠ q : ℕ, ∑ i, (-1 : ℤ) ^ q *
        (Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj (M i)) : ℤ) := by
      apply finsum_congr
      intro q
      rw [Additive.FunctorBiproductDimension.additive_functor_biproduct_finrank
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q) M
        (fun i => CoherentCohomology.proper_coherent_cohomologyFinite p (M i) q)]
      simp only [Nat.cast_sum, Finset.mul_sum]
    _ = _ := finsum_sum_comm Finset.univ _
      (fun i _ => coefficientEuler_terms_hasFiniteSupport p (M i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerBiproduct
