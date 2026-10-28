import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FiniteLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCocycle

/-! # Real Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealLift.CM

noncomputable section

/-! Construct the real lift with the source frame's sign, and prove its
exact adelic factorization with the previously constructed finite lift. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

def realLift (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : MpR :=
  if MultiplierSign.CM.sourceSign E L g = 1 then W.normalizedRealLift (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)
  else W.real.negOne * W.normalizedRealLift (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)

theorem realLift_covers (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    W.real.project (realLift E L W g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) := by
  unfold realLift
  split_ifs
  · exact W.normalizedRealLift_covers _
  · rw [map_mul, W.real.project_negOne, one_mul, W.normalizedRealLift_covers]

theorem realLift_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (GeometricSource.CM.Positions E places)) :
    W.real.action (realLift E L W g) f =
      MultiplierSign.CM.sourceSign E L g • W.real.action (W.normalizedRealLift (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) f := by
  unfold realLift
  split_ifs with h
  · rw [h, one_smul]
  · have he := (MultiplierSign.CM.sourceSign_eq_one_or_neg_one E L g).resolve_left h
    rw [map_mul, LinearEquiv.mul_apply, W.real.genuine, he]
    exact (neg_one_smul ℂ _).symm

theorem lift_factorization (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    W.includeReal (realLift E L W g) *
      W.includeFinite (SourceFinite.FiniteLift.CM.finiteLift E L W g) =
      W.rationalSplit (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) := by
  unfold realLift SourceFinite.FiniteLift.CM.finiteLift
  split_ifs
  · exact W.finiteLift_factorization _
  · rw [map_mul, map_mul]
    have hc := W.commute (W.normalizedRealLift (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) W.finite.negOne
    have hn := (W.centralProduct_kernel W.real.negOne W.finite.negOne).mpr (Or.inr ⟨rfl, rfl⟩)
    calc
      _ = (W.includeReal W.real.negOne * W.includeFinite W.finite.negOne) *
          (W.includeReal (W.normalizedRealLift (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) *
            W.includeFinite (W.finiteLift (ComplexAction.CM.Symplectic.symplectic E L.coordinates g))) := by
        rw [mul_assoc, ← mul_assoc (W.includeReal (W.normalizedRealLift _)), hc.eq]
        simp only [mul_assoc]
      _ = _ := by rw [hn, one_mul, W.finiteLift_factorization]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealLift.CM
