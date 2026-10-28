import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MixedPeriodCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates

/-! # Period Hodge Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodHodgeTransport

noncomputable section

/-! Complexify an arbitrary real change of the native period space.
The new period kernel is its literal image, and the selected embedding
coordinates transform by the prescribed complex component maps. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

def nativeTangentComplexification :
    ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) ≃ₗ[ℂ] ℂ ⊗[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)).symm.trans
    ((Intrinsic.MixedPeriodCoordinates.nativePeriodRealification A).baseChange ℝ ℂ _ _)

theorem nativeTangentComplexification_tmul (z : ℂ) (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    nativeTangentComplexification A (z ⊗ₜ[ℚ] x) = z ⊗ₜ[ℝ] x.val := by
  simp only [nativeTangentComplexification, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, Intrinsic.MixedPeriodCoordinates.nativePeriodRealification_one_tmul]

def realTangentProjection : ℂ ⊗[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (LinearMap.id : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A).liftBaseChange ℂ

theorem realTangentProjection_tmul (z : ℂ) (x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    realTangentProjection A (z ⊗ₜ[ℝ] x) = z • x := rfl

theorem complexPeriodProjection_realification (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A x = realTangentProjection A (nativeTangentComplexification A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x => rw [nativeTangentComplexification_tmul]; rfl

def realPeriodComplexification (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) ≃ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (nativeTangentComplexification A).trans
    ((u.baseChange ℝ ℂ _ _).trans (nativeTangentComplexification A).symm)

theorem realPeriodComplexification_coordinates
    (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    nativeTangentComplexification A (realPeriodComplexification A u x) =
      u.baseChange ℝ ℂ _ _ (nativeTangentComplexification A x) := by
  simp only [realPeriodComplexification, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem realPeriodComplexification_symm (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    (realPeriodComplexification A u).symm = realPeriodComplexification A u.symm := rfl

def realChangedComplexPeriodMap (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  ((u.symm.toLinearMap.restrictScalars ℚ).comp (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype).liftBaseChange ℂ

theorem realChangedComplexPeriodMap_factor (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    realChangedComplexPeriodMap A u x =
      Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A ((realPeriodComplexification A u).symm x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
    rw [realPeriodComplexification_symm, complexPeriodProjection_realification,
      realPeriodComplexification_coordinates, nativeTangentComplexification_tmul,
      LinearEquiv.baseChange_tmul, realTangentProjection_tmul]
    rfl

theorem realChangedComplexPeriodMap_kernel (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    (realChangedComplexPeriodMap A u).ker =
      (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker.map (realPeriodComplexification A u).toLinearMap := by
  ext x
  change realChangedComplexPeriodMap A u x = 0 ↔ _
  rw [realChangedComplexPeriodMap_factor]
  constructor
  · intro hx
    exact ⟨(realPeriodComplexification A u).symm x, hx,
      (realPeriodComplexification A u).apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A y = 0 at hy
    simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hy

variable (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (e : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] (Fin 3 → E))

def realSelectedPeriodCoordinates : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) :=
  (CMSelectedMixed.cmSelectedMixedCoordinates σ hσ).toLinearMap.comp (Intrinsic.MixedPeriodCoordinates.nativeMixedPeriodCoordinates E A e).toLinearMap

omit [Fintype Place] in
theorem realSelectedPeriodCoordinates_rational (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    realSelectedPeriodCoordinates A E σ hσ e x.val = fun p j => σ p (e x j) := by
  change CMSelectedMixed.cmSelectedMixedCoordinates σ hσ (Intrinsic.MixedPeriodCoordinates.nativeMixedPeriodCoordinates E A e x.val) = _
  rw [Intrinsic.MixedPeriodCoordinates.nativeMixedPeriodCoordinates_rational, CMSelectedMixed.cmSelectedMixedCoordinates_embedding]

def complexMarkedPeriodCoordinates :
    ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → Geometry.ComplexBall.PrescribedSignsB.Vec) :=
  (e.baseChange ℚ ℂ _ _).trans (RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E)

omit [NumberField.IsCMField E] in
theorem complexMarkedPeriodCoordinates_tmul (z : ℂ) (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (τ : E →ₐ[ℚ] ℂ) :
    complexMarkedPeriodCoordinates A E e (z ⊗ₜ[ℚ] x) τ = z • (fun j => τ (e x j)) := by
  funext j
  exact RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates_tmul E z (e x) τ j

omit [Fintype Place] in
theorem complexMarkedPeriodCoordinates_selected
    (p : Place) (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    complexMarkedPeriodCoordinates A E e x (σ p) =
      ((LinearMap.proj p).comp (realSelectedPeriodCoordinates A E σ hσ e)).liftBaseChange ℂ
        (nativeTangentComplexification A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z x =>
    rw [complexMarkedPeriodCoordinates_tmul, nativeTangentComplexification_tmul]
    change z • (fun j => σ p (e x j)) = z • realSelectedPeriodCoordinates A E σ hσ e x.val p
    rw [realSelectedPeriodCoordinates_rational]

omit [Fintype Place] in
theorem realPeriodComplexification_selected
    (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) (p : Place) :
    complexMarkedPeriodCoordinates A E e
        (realPeriodComplexification A (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q) x) (σ p) =
      q p (complexMarkedPeriodCoordinates A E e x (σ p)) := by
  rw [complexMarkedPeriodCoordinates_selected A E σ hσ e,
    realPeriodComplexification_coordinates, complexMarkedPeriodCoordinates_selected A E σ hσ e]
  generalize nativeTangentComplexification A x = y
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul z v =>
    rw [LinearEquiv.baseChange_tmul]
    change z • realSelectedPeriodCoordinates A E σ hσ e
      (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange E A σ hσ e q v) p =
        q p (z • realSelectedPeriodCoordinates A E σ hσ e v p)
    rw [(q p).map_smul]
    exact congrArg (fun w : Geometry.ComplexBall.PrescribedSignsB.Vec => z • w)
      (Intrinsic.MixedPeriodCoordinates.nativeMixedComponentChange_selected E A σ hσ e q v p)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodHodgeTransport
