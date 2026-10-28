import OAI.RepresentationTheory.Hecke.RadialDilation.Complexification
import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates

/-! # Split Scalar Coordinates -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization

noncomputable section

/-! The rational scalar matrix is diagonal in actual split local embedding coordinates. -/

open scoped Classical TensorProduct _root_.Matrix

variable (E K : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def splitRationalCoordinates (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ)) :
    ((E →ₐ[ℚ] K) → Fin 3 → K) ≃ₗ[K] (κ → K) :=
  (Complexification.Realization.splitRankThreeBaseChange E K).symm.trans
    ((e.baseChange ℚ K _ _).trans (TensorProduct.piScalarRight ℚ K K κ))

theorem splitRationalCoordinates_tmul (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ))
    (z : K) (x : Fin 3 → E) :
    splitRationalCoordinates E K e (Complexification.Realization.splitRankThreeBaseChange E K (z ⊗ₜ[ℚ] x)) =
      z • (fun i => algebraMap ℚ K (e x i)) := by
  simp [splitRationalCoordinates, Algebra.smul_def, mul_comm]
  rfl

def splitScalarEnd (r : E) :
    ((E →ₐ[ℚ] K) → Fin 3 → K) →ₗ[K] ((E →ₐ[ℚ] K) → Fin 3 → K) where
  toFun x σ := σ r • x σ
  map_add' x y := by funext σ; exact smul_add _ _ _
  map_smul' a x := by
    funext σ i
    change σ r * (a * x σ i) = a * (σ r * x σ i)
    ring

theorem splitScalarEnd_identification (r : E) (x : K ⊗[ℚ] (Fin 3 → E)) :
    Complexification.Realization.splitRankThreeBaseChange E K ((Complexification.Realization.rationalScalarEnd E r).baseChange K x) =
      splitScalarEnd E K r (Complexification.Realization.splitRankThreeBaseChange E K x) := by
  funext σ
  exact Complexification.Realization.splitRankThreeBaseChange_scalar E K r x σ

omit [DecidableEq κ] in
theorem rational_matrix_split_mulVec (M : Matrix κ κ ℚ) (v : κ → ℚ) :
    M.map (algebraMap ℚ K) *ᵥ (fun i => algebraMap ℚ K (v i)) =
      fun i => algebraMap ℚ K ((M *ᵥ v) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem rational_matrix_realizes_split_scalar (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ))
    (r : E) (u : (E →ₐ[ℚ] K) → Fin 3 → K) :
    splitRationalCoordinates E K e (splitScalarEnd E K r u) =
      (RationalCoordinates.Realization.rationalScalarMatrix E e r).map (algebraMap ℚ K) *ᵥ splitRationalCoordinates E K e u := by
  obtain ⟨x, rfl⟩ := (Complexification.Realization.splitRankThreeBaseChange E K).surjective u
  rw [← splitScalarEnd_identification]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, splitRationalCoordinates_tmul, splitRationalCoordinates_tmul,
        Matrix.mulVec_smul, rational_matrix_split_mulVec, RationalCoordinates.Realization.rationalScalarMatrix_apply]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization
