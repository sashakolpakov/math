import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FamilyBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldSectionIsomorphism

/-! # Universal Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a Noetherian affine tame base, a complete family of sections
of a positive canonical graph power is universally complete on all affine
tests. This uses the actual graph-power field base-change comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPower_completeSections_universal
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (m : ℕ) (hm : 0 < m)
    {r : ℕ} (s : Fin r → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower m).sheaf))
    (hs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination A.abelian.scheme.hom.appTop.hom
      (A.graphBundle.tensorPower m).sheaf s)) :
    Universal.SectionCompletenessOpen.UniversallyCompleteSectionFamily A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf s (𝟙 S) := by
  apply (ProperFlat.SectionFiberCriterion.properFlat_universalSectionCompleteness_iff_geometric A.abelian.scheme.hom
    (A.graphBundle.tensorPower m) s (𝟙 S)).mpr
  intro K _ b
  have ht := A.graphBundle_positivePower_fieldSectionTensorComparison_bijective hN hunit m hm b
  have hc := Section.FamilyBaseChange.completeSectionFamily_pullback_of_tensor_bijective
    (B := Affine.TensorSectionComparison.morphismGlobalAlgebra b) (pullback.fst A.abelian.scheme.hom b)
    A.abelian.scheme.hom.appTop.hom (A.graphBundle.tensorPower m).sheaf
    (pullback.snd A.abelian.scheme.hom b).appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility (IsPullback.of_hasPullback A.abelian.scheme.hom b)) s hs ht
  exact hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
