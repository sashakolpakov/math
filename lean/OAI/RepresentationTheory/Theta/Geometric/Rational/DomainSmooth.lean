import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM
import OAI.RepresentationTheory.Theta.Geometric.Period.Derivative

/-! # Domain Smooth -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Rational special-unitary transformations are holomorphic smooth
maps of the actual open ball domain. -/

open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rationalPeriodPoint_contMDiff (g : D.RationalSU) :
    ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) ∞ (D.rationalPeriodPoint g) := by
  apply (ContMDiff.subtypeVal_comp_iff D.domain (D.rationalPeriodPoint g)).mp
  apply Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable
  intro x
  exact (D.periodMap_differentiableAt g x).mdifferentiableAt.comp x
    ((contMDiff_subtype_val (I := 𝓘(ℂ, LinearTheta.BallCoordinates)) (U := D.domain)
      (n := ∞)).mdifferentiableAt (by simp))

end

end OAI.RepresentationTheory.Theta.Geometric
