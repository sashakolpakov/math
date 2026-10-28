import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonReturn
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleIntrinsicCotangentSlots

/-! # Intrinsic Source One Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicSourceOneForms.CM

noncomputable section

/-! The actual native ThetaOneForms cotangent form of every factor input is a
fixed nonzero scalar times the actual source theta covector. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

def nativeSourceOneFormConstant (z₀ : B.Domain) : ℂ :=
  SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q j * SingleComparisonReturn.CM.singleComparisonReturnConstant K d Q hμ j N hN L hL z₀

include hG in
theorem native_source_one_form_constant_ne_zero (z₀ : B.Domain) :
    nativeSourceOneFormConstant K d Q hμ j N hN L hL z₀ ≠ 0 :=
  mul_ne_zero (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_ne_zero K Q j)
    (SingleComparisonReturn.CM.single_comparison_return_constant_ne_zero K d Q hμ j N hN hG L hL z₀)

include hG in
theorem native_source_one_form_coordinate
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1))
    (z₀ z : B.Domain) (i : Fin 2) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      (Pi.single i 1) = nativeSourceOneFormConstant K d Q hμ j N hN L hL z₀ *
        Slots.CM.sourceThetaCoordinates K L (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val i := by
  have he : RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (Pi.single i 1) =
      Pi.single (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) i) 1 := by
    fin_cases i <;> simp [RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding]
  have ht := SingleComparisonReturn.CM.single_comparison_return_source_slot K d Q hμ j N hN hG L hL f z₀ z i
  have hg := (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricTensor_one_apply N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    (fun _ => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i))).symm.trans ht
  have hd := congrArg (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    (SingleIntrinsicCotangentSlots.CM.direct_single_native_dual_slot K d Q hμ j i)
  have hm := (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).map_smul
    (SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q j)⁻¹
    (Pi.single (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) i) 1)
  have hfirst := (hd.trans hm).symm.trans hg
  change (SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q j)⁻¹ *
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      (Pi.single (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) i) 1) = _ at hfirst
  have hθ : RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      (Pi.single i 1) = RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
        (Pi.single (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) i) 1) := by
    exact (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm_apply N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (Pi.single i 1)).trans
      (congrArg (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)) he)
  have hs := congrArg (fun t : ℂ => SingleIntrinsicCotangentSlots.CM.singleNativeCotangentScale K Q j * t) hfirst
  rw [mul_inv_cancel_left₀ (SingleIntrinsicCotangentSlots.CM.single_native_cotangent_scale_ne_zero K Q j)] at hs
  exact hθ.trans (hs.trans (mul_assoc _ _ _).symm)

include hG in
theorem native_source_one_form
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1))
    (z₀ z : B.Domain) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm N f (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) =
      nativeSourceOneFormConstant K d Q hμ j N hN L hL z₀ •
        Projection.CM.sourceThetaCovector K L (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = u 0 • (Pi.single 0 1 : HeckeCycles.GeometricSource.CM.BallChart) + u 1 • (Pi.single 1 1 : HeckeCycles.GeometricSource.CM.BallChart) := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [hu, map_add, map_smul, map_smul]
  rw [native_source_one_form_coordinate K d Q hμ j N hN hG L hL f z₀ z 0,
    native_source_one_form_coordinate K d Q hμ j N hN hG L hL f z₀ z 1]
  change _ = nativeSourceOneFormConstant K d Q hμ j N hN L hL z₀ *
    Projection.CM.sourceThetaCovector K L (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val u
  conv_rhs => rw [hu, map_add, map_smul, map_smul]
  have hc (i : Fin 2) : Projection.CM.sourceThetaCovector K L
      (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val (Pi.single i 1) =
        Slots.CM.sourceThetaCoordinates K L (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val i := by
    apply congrArg (Projection.CM.sourceThetaCovector K L
      (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val)
    funext k
    simp only [Pi.single_apply]
    split_ifs <;> rfl
  rw [hc 0, hc 1]
  simp only [smul_eq_mul]
  change _ = nativeSourceOneFormConstant K d Q hμ j N hN L hL z₀ *
    (u 0 * Slots.CM.sourceThetaCoordinates K L (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val 0 +
      u 1 * Slots.CM.sourceThetaCoordinates K L (SingleComparisonReturn.CM.singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val 1)
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicSourceOneForms.CM
