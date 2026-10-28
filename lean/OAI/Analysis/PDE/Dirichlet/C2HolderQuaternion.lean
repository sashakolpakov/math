import OAI.Analysis.Normed.Function.Holder.C2HolderOperator
import OAI.Analysis.Normed.Function.Holder.Banach.Linear
import OAI.Analysis.PDE.Dirichlet.HessianMapNorm

open Set
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

def secondJetToRealMatrixLinear {m s : ℕ} :
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) →ₗ[ℝ]
      Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ where
  toFun D := fun i j ↦ D (coordinateVector i) (coordinateVector j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondJetToRealMatrixCLM {m s : ℕ} :
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) →L[ℝ]
      Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ where
  toLinearMap := secondJetToRealMatrixLinear
  cont := by
    change Continuous (fun D : CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ ↦
      fun i j ↦ D (coordinateVector i) (coordinateVector j))
    fun_prop

def secondJetToQuaternionCLM {m s : ℕ} (e : Fin s → Q) :
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) →L[ℝ]
      Matrix (Fin m) (Fin m) Q :=
  (hessianMatrixCLM e).comp secondJetToRealMatrixCLM

/-- The manuscript's quaternionic Hessian as a bounded map of Hölder spaces. -/
def quaternionHessianField {m s : ℕ} {Ω K : Set (CoordinateSpace m s)}
    (hΩK : Ω ⊆ K) (α : ℝ) (e : Fin s → Q) :
    OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap K (Matrix (Fin m) (Fin m) Q) α :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (secondJetToQuaternionCLM e)).comp OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM

theorem quaternionHessianField_eq {m s : ℕ} {Ω K : Set (CoordinateSpace m s)}
    (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (α : ℝ) (e : Fin s → Q)
    (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) {x : CoordinateSpace m s} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α e f) ⟨x, hΩK hx⟩ =
      quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x := by
  change OAI.Analysis.Calculus.Quaternion.hessianMap e (fun i j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative f ⟨x, hΩK hx⟩
    (coordinateVector i) (coordinateVector j)) = _
  rw [← (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ f hx).2]
  rfl

end OAI.Analysis.PDE.Dirichlet
