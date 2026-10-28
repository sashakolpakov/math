import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.PointSectionGeneration

/-! # Nonzero Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The positive Euler coefficient supplies an actual nonzero section of
the original graph bundle at tame full level. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_exists_nonzero_section (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∃ s : Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.graphBundle.sheaf, s ≠ 0 := by
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  have hp : 0 < CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
      (A.graphBundle.tensorPower 1).sheaf := by
    rw [Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.abelian.scheme.hom
      A.graphBundle.tensorPowerOneIso]
    exact A.graphBundle_euler_pos_overField hN hNk
  rw [A.graphBundle_positivePower_euler_eq_sections hN hunit 1 Nat.zero_lt_one] at hp
  obtain ⟨s, hs⟩ := Closed.PointSectionGeneration.lineBundle_exists_nonzero_section_of_finrank_pos A.abelian.scheme.hom
    (A.graphBundle.tensorPower 1) (Int.natCast_pos.mp hp)
  refine ⟨s ≫ A.graphBundle.tensorPowerOneIso.hom, fun hz => hs ?_⟩
  apply (cancel_mono A.graphBundle.tensorPowerOneIso.hom).mp
  simpa only [CategoryTheory.Limits.zero_comp] using hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
