import OAI.NumberTheory.ArithmeticGroups.Lattices.JacobiLinearization
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.QuadraticBilinearRemainder

/-! # Continuous Jacobi -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousJacobi.Construction

noncomputable section

/-! Continuous Jacobi equations and their quadratic remainder bound. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance jacobiEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance jacobiEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance jacobiEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance jacobiBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance jacobiBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance jacobiBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance jacobiTrilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance jacobiTrilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance jacobiTrilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance jacobiOperator_normed : NormedAddCommGroup
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance jacobiOperator_space : NormedSpace ℝ
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance jacobiPair_normed : NormedAddCommGroup
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ]
      (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance jacobiPair_space : NormedSpace ℝ
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ]
      (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance

def continuousJacobiPair : (L →L[ℝ] L →L[ℝ] L) →L[ℝ]
    (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) :=
  ContinuousBracketChange.Construction.continuousBilinearOfFiniteDimensions
    ((JacobiLinearization.Construction.jacobiBilinear.compl₁₂ ContinuousBracketChange.Construction.finiteBilinearEquiv.symm.toLinearMap
      ContinuousBracketChange.Construction.finiteBilinearEquiv.symm.toLinearMap).compr₂ ContinuousBracketChange.Construction.finiteTrilinearEquiv.toLinearMap)

theorem continuousJacobiPair_apply (B C : L →L[ℝ] L →L[ℝ] L) (x y z : L) :
    continuousJacobiPair B C x y z = B x (C y z) - B y (C x z) - B (C x y) z := rfl

def continuousJacobiLinearization (B : L →L[ℝ] L →L[ℝ] L) :
    (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) :=
  continuousJacobiPair B + continuousJacobiPair.flip B

theorem continuousJacobiLinearization_apply (B C : L →L[ℝ] L →L[ℝ] L) :
    continuousJacobiLinearization B C = continuousJacobiPair B C + continuousJacobiPair C B := rfl

theorem continuousJacobiLinearization_eq_algebraic (B C : L →L[ℝ] L →L[ℝ] L) :
    continuousJacobiLinearization B C = ContinuousBracketChange.Construction.finiteTrilinearEquiv
      (JacobiLinearization.Construction.jacobiLinearization (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B) (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm C)) := by
  ext x y z
  rfl

theorem continuousJacobi_zero_iff (B : L →L[ℝ] L →L[ℝ] L) :
    continuousJacobiPair B B = 0 ↔ ∀ x y z, B x (B y z) = B y (B x z) + B (B x y) z := by
  constructor
  · intro h x y z
    have he := congrArg (fun C : L →L[ℝ] L →L[ℝ] L →L[ℝ] L => C x y z) h
    change B x (B y z) - B y (B x z) - B (B x y) z = 0 at he
    apply sub_eq_zero.mp
    convert he using 1
    abel
  · intro h
    ext x y z
    change B x (B y z) - B y (B x z) - B (B x y) z = 0
    rw [h]
    abel

theorem continuousJacobiLinearization_norm_bound
    (B C : L →L[ℝ] L →L[ℝ] L) (hB : continuousJacobiPair B B = 0)
    (hC : continuousJacobiPair (B + C) (B + C) = 0) :
    ‖continuousJacobiLinearization B C‖ ≤ ‖continuousJacobiPair (L := L)‖ * ‖C‖ ^ 2 := by
  rw [continuousJacobiLinearization_apply]
  exact QuadraticBilinearRemainder.Construction.bilinear_quadratic_linearization_norm_bound
    (V := L →L[ℝ] L →L[ℝ] L) (F := L →L[ℝ] L →L[ℝ] L →L[ℝ] L)
    (continuousJacobiPair (L := L)) B C hB hC

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousJacobi.Construction
