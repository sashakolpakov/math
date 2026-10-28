import OAI.Analysis.PDE.Schauder.Calculus.TransformedHessian
import OAI.Analysis.PDE.Dirichlet.C2HolderNonlinear

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {X : Type*} [MetricSpace X] {α : ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance transformedMooreDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance transformedMooreDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance transformedMooreEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance transformedMooreEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance transformedMooreSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transformedMooreSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transformedMooreMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance transformedMooreMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The transformed nonlinear operator expressed polynomially in the
unknown's jets at fixed points, and in the coordinate-map derivatives. -/
def transformedMooreField (hα : 0 ≤ α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
    (transformedHessianField hα J T p B))

theorem contDiff_transformedMooreField
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ∞ω}
    (hα : 0 ≤ α)
    {J : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α} {T : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α}
    {p : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α} {B : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α}
    (hJ : ContDiff ℝ q J) (hT : ContDiff ℝ q T)
    (hp : ContDiff ℝ q p) (hB : ContDiff ℝ q B) :
    ContDiff ℝ q (fun y => transformedMooreField hα (J y) (T y) (p y) (B y)) := by
  let L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
  have hH : ContDiff ℝ q (fun y => transformedHessianField hα (J y) (T y) (p y) (B y)) :=
    contDiff_transformedHessianField hα hJ hT hp hB
  have hQ : ContDiff ℝ q (fun y => L (transformedHessianField hα (J y) (T y) (p y) (B y))) :=
    L.contDiff.comp hH
  exact (OAI.Analysis.Normed.Function.Holder.contDiff_mooreDetField (X := X) hα n q).comp hQ

theorem transformedMooreField_identity (hα : 0 ≤ α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) :
    transformedMooreField hα (OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
      (OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) p B =
        OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) B) := by
  unfold transformedMooreField
  rw [transformedHessianField_identity]

/-- Exact agreement with the genuinely composed potential, including
the first-derivative curvature term of a nonlinear coordinate change. -/
theorem transformedMooreField_eq_composition (hα : 0 ≤ α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (u : E → ℝ) (Ψ : E → E) (x : X) (y z : E)
    (hu : ContDiffAt ℝ 2 u y) (hΨ : ContDiffAt ℝ 2 Ψ z) (hinv : Ψ z = y)
    (hJ : OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ Ψ z)
    (hT : OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ Ψ) z)
    (hp : OAI.Analysis.Normed.Function.Holder.HolderMap.value p x = fderiv ℝ u y)
    (hB : OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ u) y) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedMooreField hα J T p B) x =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u ∘ Ψ) z) := by
  rw [transformedMooreField,OAI.Analysis.Normed.Function.Holder.value_mooreDetField]
  congr 1
  change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα J T p B) x (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  congr 1
  funext i j
  rw [value_transformedHessianField,hJ,hT,hp,hB]
  have hu' : ContDiffAt ℝ 2 u (Ψ z) := by simpa only [hinv] using hu
  simpa only [hinv,Function.comp_def] using! (OAI.Analysis.PDE.Elliptic.second_fderiv_comp hu' hΨ (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)).symm

section BanachUnknown
variable {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def transformedMooreMap (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : P → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : P → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (z : P × Z) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  transformedMooreField hα (J z.1) (T z.1) (D₁ z.2) (D₂ z.2)

theorem contDiff_transformedMooreMap (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    {J : P → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α} {T : P → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α}
    {q : ℕ∞ω} (hJ : ContDiff ℝ q J) (hT : ContDiff ℝ q T) :
    ContDiff ℝ q (transformedMooreMap hα D₁ D₂ J T) :=
  contDiff_transformedMooreField hα (hJ.comp contDiff_fst) (hT.comp contDiff_fst)
    (D₁.contDiff.comp contDiff_snd) (D₂.contDiff.comp contDiff_snd)

end BanachUnknown
end OAI.Analysis.PDE.Schauder
