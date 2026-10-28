import OAI.Analysis.PDE.Schauder.Calculus.TransformedMoore

open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem second_fderiv_add_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y+g y)) x =
      fderiv ℝ (fderiv ℝ f) x+fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y+g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y+fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hfy hgy
    simpa only [Pi.add_apply] using! fderiv_add
      (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))
  exact he.fderiv_eq.trans
    (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.add
      ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt).fderiv

variable {n : ℕ} {X : Type*} [MetricSpace X] {α : ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance backgroundDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance backgroundDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance backgroundEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance backgroundEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance backgroundSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance backgroundSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance backgroundMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance backgroundMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def transformedBackgroundMooreField (hα : 0 ≤ α)
    (B₀ : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
    (B₀+transformedHessianField hα J T p B))

theorem contDiffOn_transformedBackgroundMooreField
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ∞ω} {S : Set Y}
    (hα : 0 ≤ α) {B₀ : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α}
    {J : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α} {T : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α}
    {p : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α} {B : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α}
    (hB₀ : ContDiffOn ℝ q B₀ S) (hJ : ContDiffOn ℝ q J S) (hT : ContDiffOn ℝ q T S)
    (hp : ContDiffOn ℝ q p S) (hB : ContDiffOn ℝ q B S) :
    ContDiffOn ℝ q (fun y => transformedBackgroundMooreField hα (B₀ y) (J y) (T y) (p y) (B y)) S := by
  let L : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
  have hH := hB₀.add (contDiffOn_transformedHessianField hα hJ hT hp hB)
  have hQ := L.contDiff.comp_contDiffOn hH
  exact (OAI.Analysis.Normed.Function.Holder.contDiff_mooreDetField (X := X) hα n q).comp_contDiffOn hQ

theorem transformedBackgroundMooreField_eq_composition (hα : 0 ≤ α)
    (B₀ : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (u₀ u : E → ℝ) (Ψ : E → E) (x : X) (y z : E)
    (hu₀ : ContDiffAt ℝ 2 u₀ z) (hu : ContDiffAt ℝ 2 u y)
    (hΨ : ContDiffAt ℝ 2 Ψ z) (hinv : Ψ z = y)
    (hB₀ : OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x = fderiv ℝ (fderiv ℝ u₀) z)
    (hJ : OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ Ψ z)
    (hT : OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ Ψ) z)
    (hp : OAI.Analysis.Normed.Function.Holder.HolderMap.value p x = fderiv ℝ u y)
    (hB : OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ u) y) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα B₀ J T p B) x =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z => u₀ z+u (Ψ z)) z) := by
  rw [transformedBackgroundMooreField,OAI.Analysis.Normed.Function.Holder.value_mooreDetField]
  congr 1
  change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x+OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα J T p B) x)
      (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  congr 1
  funext i j
  have hu' : ContDiffAt ℝ 2 u (Ψ z) := by simpa only [hinv] using hu
  have hadd : fderiv ℝ (fderiv ℝ (fun z => u₀ z+u (Ψ z))) z =
      fderiv ℝ (fderiv ℝ u₀) z+fderiv ℝ (fderiv ℝ (fun z => u (Ψ z))) z := by
    simpa only [Function.comp_def] using! second_fderiv_add_at hu₀ (hu'.comp z hΨ)
  rw [hadd]
  simp only [add_apply,value_transformedHessianField,hB₀,hJ,hT,hp,hB]
  congr 1
  simpa only [hinv] using! (OAI.Analysis.PDE.Elliptic.second_fderiv_comp hu' hΨ (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)).symm

end OAI.Analysis.PDE.Schauder
