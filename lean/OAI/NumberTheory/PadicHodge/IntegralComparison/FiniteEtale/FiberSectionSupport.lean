import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPrincipalSupport

/-! # Fiber Section Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionSupport

noncomputable section

/-! A lift of the selected finite-etale fiber component can be chosen
in the original affine coefficient ring with its principal open inside
any prescribed neighborhood of the whole Artinian section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section Algebra
variable (Q B R : Type u) [CommRing Q] [CommRing B] [CommRing R]
  [Algebra Q B] [Algebra Q R] [Module.Free Q B] [Module.Finite Q B]
  [Algebra.Etale Q B] (ε : B →ₐ[Q] R)

omit [Module.Free Q B] [Module.Finite Q B] in
theorem component_mul (a : B) :
    FiberSectionTrace.component Q B R ε * (1 ⊗ₜ[Q] a) =
      ε a • FiberSectionTrace.component Q B R ε := by
  have h := SectionTrace.mul R (R ⊗[Q] B)
    (FiberSectionTrace.evaluation Q B R ε)
    (FiberSectionTrace.component Q B R ε)
    (SectionTrace.component_annihilates R (R ⊗[Q] B)
      (FiberSectionTrace.evaluation Q B R ε)) (1 ⊗ₜ[Q] a)
  simpa only [FiberSectionTrace.evaluation_tmul, one_mul] using h

omit [Module.Free Q B] [Module.Finite Q B] in
theorem mul_lift (z h : B)
    (hz : (1 ⊗ₜ[Q] z : R ⊗[Q] B) = FiberSectionTrace.component Q B R ε)
    (hh : ε h = 1) :
    (1 ⊗ₜ[Q] (z*h) : R ⊗[Q] B) = FiberSectionTrace.component Q B R ε := by
  have ht : (1 ⊗ₜ[Q] (z*h) : R ⊗[Q] B) = (1 ⊗ₜ[Q] z) * (1 ⊗ₜ[Q] h) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [ht, hz, component_mul, hh, one_smul]

omit [Module.Free Q B] [Module.Finite Q B] in
theorem evaluation_lift (z : B)
    (hz : (1 ⊗ₜ[Q] z : R ⊗[Q] B) = FiberSectionTrace.component Q B R ε) :
    ε z = 1 := by
  have he := congrArg (FiberSectionTrace.evaluation Q B R ε) hz
  simpa only [FiberSectionTrace.evaluation_tmul, one_mul,
    FiberSectionTrace.component_evaluation] using he

end Algebra

variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
  (Y : Over (Spec (CommRingCat.of R)))
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  (U : Y.left.Opens) (hUa : IsAffineOpen U) (hU : ⊤ ≤ s ⁻¹ᵁ U)
  (Q : Type u) [CommRing Q] [Algebra Q R]
  [Algebra Q (Intrinsic.SmoothClosedSections.ring R Y U)]
  [Module.Free Q (Intrinsic.SmoothClosedSections.ring R Y U)]
  [Module.Finite Q (Intrinsic.SmoothClosedSections.ring R Y U)]
  [Algebra.Etale Q (Intrinsic.SmoothClosedSections.ring R Y U)]
  (ε : Intrinsic.SmoothClosedSections.ring R Y U →ₐ[Q] R)
  (hε : ε.toRingHom = (Intrinsic.SectionEvaluation.evaluation R Y s hs U hU).toRingHom)
  (W : Y.left.Opens) (hW : ⊤ ≤ s ⁻¹ᵁ W)

include hs hUa hU hε hW in
omit [Module.Free Q ↑(Intrinsic.SmoothClosedSections.ring R Y U)] [Module.Finite Q ↑(Intrinsic.SmoothClosedSections.ring R Y U)] in
theorem from_lift (z₀ : Intrinsic.SmoothClosedSections.ring R Y U)
    (hz₀ : (1 ⊗ₜ[Q] z₀ : R ⊗[Q] Intrinsic.SmoothClosedSections.ring R Y U) =
      FiberSectionTrace.component Q (Intrinsic.SmoothClosedSections.ring R Y U) R ε) :
    ∃ z : Intrinsic.SmoothClosedSections.ring R Y U,
      (1 ⊗ₜ[Q] z : R ⊗[Q] Intrinsic.SmoothClosedSections.ring R Y U) =
        FiberSectionTrace.component Q (Intrinsic.SmoothClosedSections.ring R Y U) R ε ∧
      ε z = 1 ∧ Y.left.basicOpen z ≤ W ∧ ⊤ ≤ s ⁻¹ᵁ Y.left.basicOpen z := by
  obtain ⟨h, he, hle⟩ := Intrinsic.SectionPrincipalSupport.exists_normalized R Y s hs U hU hUa W hW
  have he' : ε h = 1 := by
    change ε.toRingHom h = 1
    rw [hε]
    exact he
  let z := z₀ * h
  have hz := mul_lift Q (Intrinsic.SmoothClosedSections.ring R Y U) R ε z₀ h hz₀ he'
  have hez : ε z = 1 := evaluation_lift Q (Intrinsic.SmoothClosedSections.ring R Y U) R ε z hz
  refine ⟨z, hz, hez, ?_, ?_⟩
  · dsimp only [z]
    rw [Scheme.basicOpen_mul]
    exact inf_le_right.trans hle
  · apply Intrinsic.SectionEvaluation.principal_contains R Y s hs U hU z
    change (Intrinsic.SectionEvaluation.evaluation R Y s hs U hU).toRingHom z = 1
    rw [← hε]
    exact hez

include hs hUa hU hε hW in
theorem exists_supported (h : Function.Surjective (algebraMap Q R)) :
    ∃ z : Intrinsic.SmoothClosedSections.ring R Y U,
      (1 ⊗ₜ[Q] z : R ⊗[Q] Intrinsic.SmoothClosedSections.ring R Y U) =
        FiberSectionTrace.component Q (Intrinsic.SmoothClosedSections.ring R Y U) R ε ∧
      ε z = 1 ∧ Y.left.basicOpen z ≤ W ∧ ⊤ ≤ s ⁻¹ᵁ Y.left.basicOpen z := by
  obtain ⟨z, hz, _⟩ := FiberSectionTrace.exists_lift Q
    (Intrinsic.SmoothClosedSections.ring R Y U) R ε h
  exact from_lift R Y s hs U hUa hU Q ε hε W hW z hz

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionSupport
