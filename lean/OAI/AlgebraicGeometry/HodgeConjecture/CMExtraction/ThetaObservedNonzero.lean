import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action

/-! # Theta Observed Nonzero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaObservedNonzero.Intrinsic

noncomputable section

/-! A nonzero observed period covector forces every canonical algebraic theta lift to be nonzero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
  (c : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)

theorem canonicalTheta_lift_ne_zero
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (hΘ : D.IsCanonicalThetaLift hg j c Θ)
    (φ : D.sphericalInputs) (x : D.domain) (hx : D.thetaUniversal φ.val x.val ≠ 0) : Θ φ ≠ 0 := by
  intro hzero
  obtain ⟨p, hp⟩ := hΘ.1 x
  have h := hΘ.2.1 φ x p hp
  rw [hzero, map_zero, map_zero] at h
  exact hx h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaObservedNonzero.Intrinsic
