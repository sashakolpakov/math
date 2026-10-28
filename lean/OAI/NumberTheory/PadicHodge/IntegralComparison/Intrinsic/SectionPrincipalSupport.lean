import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation
import Mathlib.RingTheory.Artinian.Ring

/-! # Section Principal Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPrincipalSupport

noncomputable section

/-! A principal neighborhood inside any prescribed neighborhood of an
Artinian section can be cut out by a function whose actual section
evaluation is one. The function stays in the original affine ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  (U : Y.left.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U)

theorem evaluation_isUnit (a : SmoothClosedSections.ring R Y U)
    (ha : ⊤ ≤ s ⁻¹ᵁ Y.left.basicOpen a) :
    IsUnit (SectionEvaluation.evaluation R Y s hs U hU a) := by
  have hres := Y.left.toRingedSpace.isUnit_res_basicOpen a
  have he := hres.map
    (SectionEvaluation.evaluation R Y s hs (Y.left.basicOpen a) ha).toRingHom
  change IsUnit (SectionEvaluation.evaluation R Y s hs (Y.left.basicOpen a) ha
    (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map
      (homOfLE (Y.left.basicOpen_le a)).op).hom a)) at he
  rwa [SectionEvaluation.restriction R Y s hs U hU
    (Y.left.basicOpen a) (Y.left.basicOpen_le a) ha a] at he

variable [IsArtinianRing R] [IsLocalRing R]
  (hUa : IsAffineOpen U) (W : Y.left.Opens) (hW : ⊤ ≤ s ⁻¹ᵁ W)

include hUa hW in
theorem exists_normalized : ∃ h : SmoothClosedSections.ring R Y U,
    SectionEvaluation.evaluation R Y s hs U hU h = 1 ∧
      Y.left.basicOpen h ≤ W := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let p : Spec (CommRingCat.of R) := Classical.ofNonempty
  have hpU : s p ∈ U := hU (show p ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  have hpW : s p ∈ W := hW (show p ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  obtain ⟨a, haW, hpa⟩ := hUa.exists_basicOpen_le ⟨s p, hpW⟩ hpU
  change SmoothClosedSections.ring R Y U at a
  have ha : ⊤ ≤ s ⁻¹ᵁ Y.left.basicOpen a := by
    intro q _
    have hqp : q = p := Subsingleton.elim _ _
    subst q
    exact hpa
  obtain ⟨v, hv⟩ := evaluation_isUnit R Y s hs U hU a ha
  refine ⟨a * algebraMap R (SmoothClosedSections.ring R Y U) (↑(v⁻¹) : R), ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes, ← hv]
    exact v.mul_inv
  · rw [Scheme.basicOpen_mul]
    exact inf_le_left.trans haW

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPrincipalSupport
