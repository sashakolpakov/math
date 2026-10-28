import OAI.RepresentationTheory.Weil.UnitarySplitting.HaarScaling
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Field Modulus -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FieldModulus.Construction

noncomputable section

/-! The multiplicative character measuring the scaling of additive Haar
measure by field multiplication. -/

open _root_.MeasureTheory
open scoped NNReal

def fieldDilation {F : Type} [NormedField F] (a : Fˣ) : F ≃ₜ+ F where
  toFun x := (a : F) * x
  invFun x := (↑a⁻¹ : F) * x
  left_inv x := by dsimp only; rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by dsimp only; rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := mul_add _ x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem fieldDilation_one {F : Type} [NormedField F] :
    fieldDilation (1 : Fˣ) = ContinuousAddEquiv.refl F := by
  ext x
  exact one_mul x

theorem fieldDilation_mul {F : Type} [NormedField F] (a b : Fˣ) :
    fieldDilation (a * b) = (fieldDilation b).trans (fieldDilation a) := by
  ext x
  exact mul_assoc (a : F) (b : F) x

def fieldModulus (F : Type) [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] : Fˣ →* ℝ≥0 where
  toFun a := addEquivAddHaarChar (fieldDilation a)
  map_one' := by rw [fieldDilation_one, addEquivAddHaarChar_refl]
  map_mul' a b := by rw [fieldDilation_mul, addEquivAddHaarChar_trans, mul_comm]

theorem fieldModulus_pos {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] (a : Fˣ) : 0 < fieldModulus F a :=
  addEquivAddHaarChar_pos (fieldDilation a)

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
variable (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))

def continuousFieldAutomorphism (σ : E ≃ₐ[F] E) : E ≃ₜ+ E where
  toAddEquiv := σ.toAddEquiv
  continuous_toFun := QuadraticNorm.Construction.fieldAutomorphism_continuous hF hEmbedding σ
  continuous_invFun := QuadraticNorm.Construction.fieldAutomorphism_continuous hF hEmbedding σ.symm

include hF hEmbedding in
omit [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F] in
theorem fieldModulus_conjugate (σ : E ≃ₐ[F] E) (b : Eˣ) :
    fieldModulus E (Units.map σ.toMonoidHom b) = fieldModulus E b := by
  exact (HaarScaling.Construction.addHaarChar_intertwining (continuousFieldAutomorphism hF hEmbedding σ)
    (fieldDilation b) (fieldDilation (Units.map σ.toMonoidHom b))
    (fun x => map_mul σ (b : E) x)).symm

include hF hEmbedding in
theorem fieldModulus_base [SecondCountableTopology F]
    (hQuadratic : Module.finrank F E = 2) (a : Fˣ) :
    fieldModulus E (Units.map (algebraMap F E).toMonoidHom a) = fieldModulus F a ^ 2 := by
  let e := (QuadraticNorm.Construction.quadraticFieldCoordinates hF hEmbedding hQuadratic).trans
    (ContinuousLinearEquiv.finTwoArrow F F)
  have he (x : E) :
      e (fieldDilation (Units.map (algebraMap F E).toMonoidHom a) x) =
        HaarScaling.Construction.continuousProdAddEquiv (fieldDilation a) (fieldDilation a) (e x) := by
    change e (algebraMap F E (a : F) * x) = ((a : F) * (e x).1, (a : F) * (e x).2)
    rw [← Algebra.smul_def, e.map_smul]
    rfl
  have hh := HaarScaling.Construction.addHaarChar_intertwining e.toContinuousAddEquiv
    (fieldDilation (Units.map (algebraMap F E).toMonoidHom a))
    (HaarScaling.Construction.continuousProdAddEquiv (fieldDilation a) (fieldDilation a)) he
  rw [HaarScaling.Construction.addHaarChar_prod] at hh
  exact hh.trans (pow_two (fieldModulus F a)).symm

include hF hEmbedding in
theorem fieldModulus_norm [CharZero F] [SecondCountableTopology F]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (hne : ∃ z : E, σ z ≠ z) (b : Eˣ) :
    fieldModulus E b = fieldModulus F (Units.map (Algebra.norm F) b) := by
  have hnorm : b * Units.map σ.toMonoidHom b =
      Units.map (algebraMap F E).toMonoidHom (Units.map (Algebra.norm F) b) := by
    apply Units.ext
    exact (QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne (b : E)).symm
  have hh := congrArg (fieldModulus E) hnorm
  rw [map_mul, fieldModulus_conjugate hF hEmbedding σ b,
    fieldModulus_base hF hEmbedding hQuadratic] at hh
  have hs : fieldModulus E b ^ 2 = fieldModulus F (Units.map (Algebra.norm F) b) ^ 2 := by
    simpa only [pow_two] using hh
  exact (pow_left_inj₀ zero_le zero_le (by decide : (2 : ℕ) ≠ 0)).mp hs

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FieldModulus.Construction
