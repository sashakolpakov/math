import OAI.RepresentationTheory.Theta.Geometric.Period.Quotient
import OAI.NumberTheory.ArithmeticGroups.Action

/-! # Action -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The integral CM action in the explicit period quotient coordinates is
diagonal and independent of the ball coordinate. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.quotientCharacter (i : Fin s) (j : Fin 3) : E →+* ℂ :=
  if i = D.pel.reference.distinguished then
    if j = 2 then (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom
    else (D.pel.reference.embeddings i).toRingHom
  else if D.pel.reference.compactSigns i then (D.pel.reference.embeddings i).toRingHom
  else (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom

def Data.ActiveHeckeThetaData.periodScalarAction : E →+* Module.End ℂ (Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) where
  toFun a :=
    { toFun := fun t i j => D.quotientCharacter i j a * t i j
      map_add' := by intro u v; funext i j; exact mul_add _ _ _
      map_smul' := by intro c u; funext i j; change _ * (c * _) = c * (_ * _); ring }
  map_zero' := by
    apply LinearMap.ext
    intro t
    funext i j
    change D.quotientCharacter i j 0 * t i j = 0
    rw [map_zero, zero_mul]
  map_one' := by
    apply LinearMap.ext
    intro t
    funext i j
    change D.quotientCharacter i j 1 * t i j = t i j
    rw [map_one, one_mul]
  map_add' a b := by
    apply LinearMap.ext
    intro t
    funext i j
    change D.quotientCharacter i j (a + b) * t i j =
      D.quotientCharacter i j a * t i j + D.quotientCharacter i j b * t i j
    rw [map_add, add_mul]
  map_mul' a b := by
    apply LinearMap.ext
    intro t
    funext i j
    change D.quotientCharacter i j (a * b) * t i j =
      D.quotientCharacter i j a * (D.quotientCharacter i j b * t i j)
    rw [map_mul, mul_assoc]

theorem Data.ActiveHeckeThetaData.periodProjection_ambientAction (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : E)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    D.periodProjection z (NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction D.pel.reference.embeddings a u) =
      D.periodScalarAction a (D.periodProjection z u) := by
  funext i j
  by_cases hi : i = D.pel.reference.distinguished
  · subst i
    fin_cases j <;>
      simp [Data.ActiveHeckeThetaData.periodProjection, Period.Quotient.activePeriodProjection, NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction,
        Data.ActiveHeckeThetaData.periodScalarAction, Data.ActiveHeckeThetaData.quotientCharacter, Pi.smul_apply, smul_eq_mul] <;> ring
  · cases hd : D.pel.reference.compactSigns i <;>
      simp [Data.ActiveHeckeThetaData.periodProjection, NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction, Data.ActiveHeckeThetaData.periodScalarAction,
        Data.ActiveHeckeThetaData.quotientCharacter, hi, hd, Pi.smul_apply, smul_eq_mul]

def Data.ActiveHeckeThetaData.periodScalarEquiv (a : E) (ha : a ≠ 0) :
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ≃ₗ[ℂ] Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) where
  toLinearMap := D.periodScalarAction a
  invFun := D.periodScalarAction a⁻¹
  left_inv t := by
    change (D.periodScalarAction a⁻¹ * D.periodScalarAction a) t = t
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
    rfl
  right_inv t := by
    change (D.periodScalarAction a * D.periodScalarAction a⁻¹) t = t
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    rfl

end

end OAI.RepresentationTheory.Theta.Geometric
