import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Quotient
import OAI.NumberTheory.ArithmeticGroups.Action

/-! # Quotient Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The integral CM action in the explicit period quotient coordinates is
diagonal and independent of the ball coordinate. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

def Datum.RankThreePELDatum.quotientCharacter (i : Fin s) (j : Fin 3) : E →+* ℂ :=
  if i = P.distinguished then
    if j = 2 then (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom
    else (P.embeddings i).toRingHom
  else if P.compactSigns i then (P.embeddings i).toRingHom
  else (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom

def Datum.RankThreePELDatum.periodScalarAction : E →+* Module.End ℂ (Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s)) where
  toFun a :=
    { toFun := fun t i j => P.quotientCharacter i j a * t i j
      map_add' := by intro u v; funext i j; exact mul_add _ _ _
      map_smul' := by intro c u; funext i j; change _ * (c * _) = c * (_ * _); ring }
  map_zero' := by
    apply LinearMap.ext
    intro t
    funext i j
    change P.quotientCharacter i j 0 * t i j = 0
    rw [map_zero, zero_mul]
  map_one' := by
    apply LinearMap.ext
    intro t
    funext i j
    change P.quotientCharacter i j 1 * t i j = t i j
    rw [map_one, one_mul]
  map_add' a b := by
    apply LinearMap.ext
    intro t
    funext i j
    change P.quotientCharacter i j (a + b) * t i j =
      P.quotientCharacter i j a * t i j + P.quotientCharacter i j b * t i j
    rw [map_add, add_mul]
  map_mul' a b := by
    apply LinearMap.ext
    intro t
    funext i j
    change P.quotientCharacter i j (a * b) * t i j =
      P.quotientCharacter i j a * (P.quotientCharacter i j b * t i j)
    rw [map_mul, mul_assoc]

omit [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.periodProjection_ambientAction (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : E)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    P.periodProjection z (NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction P.embeddings a u) =
      P.periodScalarAction a (P.periodProjection z u) := by
  funext i j
  by_cases hi : i = P.distinguished
  · subst i
    fin_cases j <;>
      simp [Datum.RankThreePELDatum.periodProjection, Reference.Quotient.activePeriodProjection, NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction,
        Datum.RankThreePELDatum.periodScalarAction, Datum.RankThreePELDatum.quotientCharacter, Pi.smul_apply, smul_eq_mul] <;> ring
  · cases hd : P.compactSigns i <;>
      simp [Datum.RankThreePELDatum.periodProjection, NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction, Datum.RankThreePELDatum.periodScalarAction,
        Datum.RankThreePELDatum.quotientCharacter, hi, hd, Pi.smul_apply, smul_eq_mul]

def Datum.RankThreePELDatum.periodScalarEquiv (a : E) (ha : a ≠ 0) :
    Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s) ≃ₗ[ℂ] Datum.RankThreePELDatum.PeriodQuotientCoordinates (s := s) where
  toLinearMap := P.periodScalarAction a
  invFun := P.periodScalarAction a⁻¹
  left_inv t := by
    change (P.periodScalarAction a⁻¹ * P.periodScalarAction a) t = t
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
    rfl
  right_inv t := by
    change (P.periodScalarAction a * P.periodScalarAction a⁻¹) t = t
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
