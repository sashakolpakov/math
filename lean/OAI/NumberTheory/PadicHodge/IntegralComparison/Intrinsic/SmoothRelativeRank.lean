import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RelativeRank

/-! # Smooth Relative Rank -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothRelativeRank

noncomputable section

/-! Relative dimension computes the rank of differentials with the
original coefficient algebra used by the native de Rham construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]

theorem locally_standard (X : Over (Spec (CommRingCat.of R))) (g : ℕ)
    [SmoothOfRelativeDimension g X.hom] (U : X.left.Opens) (hU : IsAffineOpen U) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R (SmoothClosedSections.ring R X U)) := by
  have h : SmoothOfRelativeDimension (0 + g) (hU.fromSpec ≫ X.hom) := inferInstance
  rw [Nat.zero_add, AffineOpen.SectionBase.overBase R X U hU] at h
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).mp h

theorem sections (X : Over (Spec (CommRingCat.of R))) (g : ℕ)
    [SmoothOfRelativeDimension g X.hom] (U : X.left.Opens) (hU : IsAffineOpen U)
    (p : PrimeSpectrum (SmoothClosedSections.ring R X U)) : Module.rankAtStalk Ω[SmoothClosedSections.ring R X U⁄R] p = g := by
  let := SmoothOfRelativeDimension.smooth g X.hom
  let := SmoothClosedSections.smooth_sections R X U hU
  exact Smooth.RelativeRank.locally_standard_smooth_rank R (SmoothClosedSections.ring R X U) g
    (locally_standard R X g U hU) p

theorem quotient (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [IsClosedImmersion f.left] (g : ℕ) [SmoothOfRelativeDimension g X.hom]
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (p : PrimeSpectrum (SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩)) :
    Module.rankAtStalk Ω[SmoothClosedSections.ring R Y U ⧸ f.left.ker.ideal ⟨U, hU⟩⁄R] p = g := by
  let := SmoothOfRelativeDimension.smooth g X.hom
  let := SmoothClosedSections.smooth_quotient R X Y f U hU
  exact Smooth.RelativeRank.locally_standard_smooth_rank R _ g
    (Smooth.RelativeRank.locally_standard_smooth_of_equiv g
      (SmoothClosedSections.quotientEquiv R X Y f U hU).symm
      (locally_standard R X g (f.left ⁻¹ᵁ U) (hU.preimage f.left))) p

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothRelativeRank
