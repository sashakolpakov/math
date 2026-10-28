import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldCohomologyModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

/-! # Line Bundle Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleEuler

noncomputable section

/-! Proper line bundles have finite-dimensional, bounded cohomology and an Euler characteristic computed by an actual finite projective model. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem properField_lineBundle_cohomology_bounded
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) :
    ∃ N, ∀ q, N ≤ q → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj L.sheaf) := by
  obtain ⟨D, ⟨N, hb⟩, _, _, he⟩ := FieldCohomologyModel.properField_lineBundle_exists_finite_cohomology_model p L
  refine ⟨N, fun q hq => ?_⟩
  exact (he q).some.isZero_iff.mp (HomologicalComplex.ExactAt.of_isZero (hb q hq)).isZero_homology

theorem properField_lineBundle_euler_finite_model
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) :
    ∃ (N : ℕ) (D : CochainComplex (ModuleCat.{u} K) ℕ),
      (∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite K (D.X q)) ∧ (∀ q, Module.Projective K (D.X q)) ∧
      (∀ q, Nonempty (D.homology q ≅
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj L.sheaf)) ∧
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf =
        ∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * (Module.finrank K (D.X q) : ℤ) := by
  obtain ⟨D, ⟨N, hb⟩, hf, hp, he⟩ := FieldCohomologyModel.properField_lineBundle_exists_finite_cohomology_model p L
  exact ⟨N, D, hb, hf, hp, he,
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_finite_model p L.sheaf D N hf hb (fun q => (he q).some)⟩

theorem coefficientEulerCharacteristic_eq_of_sheafIso
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    {M Q : X.Modules} (e : M ≅ Q) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p Q := by
  apply finsum_congr
  intro q
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ))
    (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).mapIso e).toLinearEquiv.finrank_eq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleEuler
