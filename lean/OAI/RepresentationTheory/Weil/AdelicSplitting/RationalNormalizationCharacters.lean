import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct

/-! # Rational Normalization Characters -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalNormalizationCharacters.Construction

noncomputable section

/-! The character factors in the corrected local normalization have
product one on rational inputs. This follows directly from the supplied
principal-character and norm-restriction conditions. -/

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (C : Characters.Construction.GlobalCharacters F d n m)

include C in
theorem normCharacterScalar_principal_n_hasProd (x : F) :
    HasProd (fun v => Normalization.Construction.normCharacterScalar F d v (ArchimedeanAdeles.Construction.rationalScalar F v x) ^ n) 1 := by
  by_cases hx : x = 0
  · subst x
    apply (hasProd_one : HasProd (fun _ : ArchimedeanAdeles.Construction.Places F => (1 : Circle)) 1).congr_fun
    intro v
    simp [Normalization.Construction.normCharacterScalar]
  · have h := CharacterProduct.Construction.globalCharacters_norm_n_hasProd F d n m C (Units.mk0 x hx)
    apply h.congr_fun
    intro v
    have hv : ArchimedeanAdeles.Construction.rationalScalar F v x ≠ 0 := by simpa only [map_zero] using (ArchimedeanAdeles.Construction.rationalScalar F v).injective.ne hx
    rw [Normalization.Construction.normCharacterScalar, dite_eq_left hv]
    congr 2
    exact Units.ext rfl

include C in
theorem normCharacterScalar_principal_m_hasProd (x : F) :
    HasProd (fun v => Normalization.Construction.normCharacterScalar F d v (ArchimedeanAdeles.Construction.rationalScalar F v x) ^ m) 1 := by
  by_cases hx : x = 0
  · subst x
    apply (hasProd_one : HasProd (fun _ : ArchimedeanAdeles.Construction.Places F => (1 : Circle)) 1).congr_fun
    intro v
    simp [Normalization.Construction.normCharacterScalar]
  · have h := CharacterProduct.Construction.globalCharacters_norm_m_hasProd F d n m C (Units.mk0 x hx)
    apply h.congr_fun
    intro v
    have hv : ArchimedeanAdeles.Construction.rationalScalar F v x ≠ 0 := by simpa only [map_zero] using (ArchimedeanAdeles.Construction.rationalScalar F v).injective.ne hx
    rw [Normalization.Construction.normCharacterScalar, dite_eq_left hv]
    congr 2
    exact Units.ext rfl

def firstFactorCharacter (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) : Circle :=
  Normalization.Construction.normCharacterScalar F d v ((Normalization.Construction.localDelta F d hd v)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K).val.re ^ n *
    Characters.Construction.localCharacter F d C.χW v
      ((Normalization.Construction.localDelta F d hd v) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u)

def secondFactorCharacter (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) : Circle :=
  Normalization.Construction.normCharacterScalar F d v (Matrix.GeneralLinearGroup.det H).val.re ^ m *
    Characters.Construction.localCharacter F d C.χV v (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u)

theorem firstFactorCharacter_principal_hasProd
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (u : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ) :
    HasProd (fun v => firstFactorCharacter F d hd n m C v
      (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)) 1 := by
  let b : (UnitaryBase.Construction.Quadratic F d)ˣ := (Normalization.Construction.deltaUnit d hd)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K
  let z : (UnitaryBase.Construction.Quadratic F d)ˣ := (Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u
  have h := (normCharacterScalar_principal_n_hasProd F d n m C b.val.re).mul
    (CharacterProduct.Construction.globalCharacters_chiW_hasProd F d n m C z)
  rw [one_mul] at h
  apply h.congr_fun
  intro v
  dsimp only [firstFactorCharacter]
  simp only [Assembly.Construction.localDelta_eq_map, Assembly.Construction.determinant_localizedUnit, ← map_pow, ← map_inv, ← map_mul]
  rfl

theorem secondFactorCharacter_principal_hasProd
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (u : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ) :
    HasProd (fun v => secondFactorCharacter F d n m C v
      (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)) 1 := by
  have h := (normCharacterScalar_principal_m_hasProd F d n m C (Matrix.GeneralLinearGroup.det H).val.re).mul
    (CharacterProduct.Construction.globalCharacters_chiV_hasProd F d n m C (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u))
  rw [one_mul] at h
  apply h.congr_fun
  intro v
  dsimp only [secondFactorCharacter]
  simp only [Assembly.Construction.determinant_localizedUnit, ← map_mul]
  rfl

theorem correctedFirstFactorScalar_eq_character (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :
    CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v H K u =
      (CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ (n * m) *
        (firstFactorCharacter F d hd n m C v H K u : ℂ) := by
  simp only [CorrectedNormalization.Construction.correctedFirstFactorScalar, firstFactorCharacter, Circle.coe_mul, Circle.coe_pow, mul_assoc]

theorem correctedSecondFactorScalar_eq_character (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :
    CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v H K u =
      (CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v) (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ (n * m) *
        (secondFactorCharacter F d n m C v H K u : ℂ) := by
  simp only [CorrectedNormalization.Construction.correctedSecondFactorScalar, secondFactorCharacter, Circle.coe_mul, Circle.coe_pow, mul_assoc]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalNormalizationCharacters.Construction
