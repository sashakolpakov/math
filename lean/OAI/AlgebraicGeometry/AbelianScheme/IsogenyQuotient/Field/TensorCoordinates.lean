import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RationalSplitCompletion
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.TensorCoordinates.Construction

noncomputable section

/-!
An E-basis gives coordinates on each actual rational split factor after
extension to Q_q. The coordinate formula retains the original E-action,
so its eigenspaces can be compared to the actual completed Tate action.
-/

open scoped TensorProduct

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {V : Type*} [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]
  {d : ℕ} (b : Module.Basis (Fin d) E V)

def fieldTensorCoordinates : ℚ_[q] ⊗[ℚ] V ≃ₗ[ℚ_[q]] (Fin d → Gal(E/ℚ) → ℚ_[q]) :=
  (LinearEquiv.baseChange ℚ ℚ_[q] _ _ (b.equivFun.restrictScalars ℚ)).trans
    ((TensorProduct.piRight ℚ ℚ_[q] ℚ_[q] (fun _ : Fin d => E)).trans
      (LinearEquiv.piCongrRight fun _ : Fin d => (RationalSplitCompletion.Construction.l45RationalCompletionEquiv j iota hsplit).toLinearEquiv))

theorem fieldTensorCoordinates_tmul (a : ℚ_[q]) (v : V) (i : Fin d) (τ : Gal(E/ℚ)) :
    fieldTensorCoordinates j iota hsplit b (a ⊗ₜ[ℚ] v) i τ =
      a * RationalSplitCompletion.Construction.l45FieldCharacter j iota τ (b.equivFun v i) := by
  change RationalSplitCompletion.Construction.l45RationalCompletionMap j iota (a ⊗ₜ[ℚ] (b.equivFun v i)) τ = _
  rfl

theorem fieldTensorCoordinates_scalar_action (r : E) (x : ℚ_[q] ⊗[ℚ] V) (i : Fin d) (τ : Gal(E/ℚ)) :
    fieldTensorCoordinates j iota hsplit b ((Algebra.lsmul ℚ ℚ V r).baseChange ℚ_[q] x) i τ =
      RationalSplitCompletion.Construction.l45FieldCharacter j iota τ r * fieldTensorCoordinates j iota hsplit b x i τ := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, fieldTensorCoordinates_tmul, fieldTensorCoordinates_tmul]
    change a * RationalSplitCompletion.Construction.l45FieldCharacter j iota τ (b.equivFun (r • v) i) = _
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, mul_add]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.TensorCoordinates.Construction
