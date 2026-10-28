import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedSlots
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSubspaces
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase

/-! # Intrinsic Lagrangian Continuity -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianContinuity.Intrinsic

noncomputable section

/-! The explicit normalized top forms descend from compact frames to
their actual moved Hodge subspaces, with the quotient topology. Their
dependence on these Lagrangian choices is continuous in the topology of
all derivatives on compact subsets of the ball. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSubspaces.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedSlots.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.IntrinsicCompactFamily OAI.RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

theorem smooth_section_ext {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s t : IntrinsicSmooth.IntrinsicSections.SmoothSection V) (h : ∀ z, s.value z = t.value z) : s = t := by
  cases s with
  | mk s hs =>
    cases t with
    | mk t ht =>
      have he : s = t := funext h
      cases he
      rfl

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A, Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hCp : ∀ p, Adelic.DataTheta.CoordinateIdentification (Bp p) P) (hGp : ∀ p, Adelic.DataTheta.GeometryIdentification (Bp p))
variable (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))

theorem normalized_top_same_subspace (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (p q : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (he : (IntrinsicCompactSubspaces.Intrinsic.compactSubspaceSetoid A).r p q) :
    IntrinsicNormalizedBase.IntrinsicCompactFamily.compactNormalizedTopSection B Bp hC hG hCp hGp hL hE f p =
      IntrinsicNormalizedBase.IntrinsicCompactFamily.compactNormalizedTopSection B Bp hC hG hCp hGp hL hE f q := by
  apply smooth_section_ext
  intro z
  rw [IntrinsicNormalizedBase.IntrinsicCompactFamily.compact_normalized_top_value,IntrinsicNormalizedBase.IntrinsicCompactFamily.compact_normalized_top_value,
    IntrinsicFixedSlots.Intrinsic.normalized_top_fixed_slots p B (Bp p) hC (hCp p) hG (hGp p),
    IntrinsicFixedSlots.Intrinsic.normalized_top_fixed_slots q B (Bp q) hC (hCp q) hG (hGp q),
    IntrinsicCompactSubspaces.Intrinsic.same_subspace_period p B (Bp p) hC (hCp p) hG (hGp p) q (Bp q) (hCp q) (hGp q) z (he z)]

def lagrangianTopSection (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : IntrinsicCompactSubspaces.Intrinsic.CompactLagrangianChoice A → IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  Quotient.lift (IntrinsicNormalizedBase.IntrinsicCompactFamily.compactNormalizedTopSection B Bp hC hG hCp hGp hL hE f)
    (normalized_top_same_subspace B Bp hC hG hCp hGp hL hE f)

theorem lagrangian_top_continuous (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    Continuous (lagrangianTopSection B Bp hC hG hCp hGp hL hE f) := by
  apply Continuous.quotient_lift
  exact IntrinsicNormalizedBase.IntrinsicCompactFamily.compact_normalized_top_continuous B Bp hC hG hCp hGp hL hE f

theorem lagrangian_top_base (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) :
    (lagrangianTopSection B Bp hC hG hCp hGp hL hE f
      (Quotient.mk (IntrinsicCompactSubspaces.Intrinsic.compactSubspaceSetoid A) (IntrinsicCompactChoices.Intrinsic.identityChoice A))).value z = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z :=
  IntrinsicNormalizedBase.Intrinsic.normalized_top_identity B hG f z

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianContinuity.Intrinsic
