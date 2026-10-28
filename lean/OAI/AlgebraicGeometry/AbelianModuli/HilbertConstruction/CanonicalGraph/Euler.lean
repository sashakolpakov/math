import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldCohomology

/-! # Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every positive canonical graph-bundle power has Euler characteristic equal to the dimension of its actual global sections over the ground field. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_euler_eq_sections
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤))) (m : ℕ) (hm : 0 < m) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf =
      (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower m).sheaf) : ℤ) :=
  CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing A.abelian.scheme.hom
    (A.graphBundle.tensorPower m).sheaf
    (fun q => A.graphBundle_positivePower_cohomology_vanishes_overField hN hunit m hm q)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_sections_finite_overField
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (m : ℕ) :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      (A.graphBundle.tensorPower m).sheaf) := by
  have : (A.graphBundle.tensorPower m).sheaf.IsQuasicoherent := (A.graphBundle.tensorPower m).isQuasicoherent
  have : (A.graphBundle.tensorPower m).sheaf.IsFiniteType := (A.graphBundle.tensorPower m).isFiniteType
  have := Proper.CoherentCohomology.proper_coherent_cohomologyFinite A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf 0
  exact Module.Finite.equiv (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
    (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) (A.graphBundle.tensorPower m).sheaf)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_positivePower_euler_nonnegative
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of K), ⊤))) (m : ℕ) (hm : 0 < m) :
    0 ≤ CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf := by
  rw [A.graphBundle_positivePower_euler_eq_sections hN hunit m hm]
  exact Int.natCast_nonneg _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
