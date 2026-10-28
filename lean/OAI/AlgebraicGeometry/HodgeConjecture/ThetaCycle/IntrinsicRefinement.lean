import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalCovers
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AlgebraicPeriodMap

/-! # Intrinsic Refinement -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRefinement.CM

noncomputable section

/-! Algebraize the derived principal-quotient map using the verified native
projective algebraization theorem. The local sheets and canonical positive
degree law are proved, so level divisibility alone constructs the refinement
between two already-given principal ball surfaces. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem principal_refinement_of_dvd
    {K : IntermediateField ℚ ℂ} [NumberField K] [NumberField.IsCMField K]
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N M : ℕ)
    (S : Cm.PrincipalBallSurface K B N) (T : Cm.PrincipalBallSurface K B M)
    (hNM : N ∣ M) : Nonempty (Cm.PrincipalRefinement K S T) := by
  obtain ⟨f, hover, hcover, hsurj, hlocal, degree, hpos, hdegree⟩ :=
    PrincipalCovers.CM.principal_analytic_refinement B N M S T hNM
  let F : C(T.surface.variety.analyticSpace, S.surface.variety.analyticSpace) :=
    ⟨f, hcover.continuous⟩
  obtain ⟨g, hg⟩ := ComplexMultiplication.HodgeComparison.AlgebraicPeriodMap.CM.Construction.exists_algebraic_map_of_holomorphic
    T.surface.variety S.surface.variety F (hlocal.mdifferentiable one_ne_zero)
  have hg_over : ∀ z : B.Domain,
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g) (T.projection z) = S.projection z := by
    intro z
    change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) (T.projection z) = S.projection z
    rw [hg]
    exact hover z
  obtain ⟨p, hp⟩ := PrincipalCovers.CM.refinement_of_principal_algebraic_map B N M S T hNM g hg_over
  exact ⟨p⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRefinement.CM
