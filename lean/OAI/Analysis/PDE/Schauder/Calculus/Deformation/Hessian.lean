import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Zero
import OAI.Analysis.PDE.Schauder.Calculus.HolderPeriodicity

open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance deformationHessianDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance deformationHessianDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance deformationHessianEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance deformationHessianEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance deformationHessianSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance deformationHessianSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance deformationHessianMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance deformationHessianMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def DeformationFields.hessianField (C : DeformationFields r α I Φ B₀ f) (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (p : ℝ × Z) : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
    (C.background p.1+transformedHessianField hα (C.jacobian p.1)
      (C.curvature p.1) (D₁ p.2) (D₂ p.2))

theorem DeformationFields.hessianField_zero_general
    (C : DeformationFields r α I Φ B₀ f) (h0 : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) (v : Z) :
    C.hessianField hα D₁ D₂ (0,v) =
      OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) (C.background 0+D₂ v) := by
  unfold DeformationFields.hessianField
  rw [C.jacobian_zero h0 hΦ,C.curvature_zero h0 hΦ,transformedHessianField_identity]

theorem DeformationFields.contDiffOn_hessianField
    (C : DeformationFields r α I Φ B₀ f) (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) :
    ContDiffOn ℝ ∞ (C.hessianField hα D₁ D₂) {p | p.1 ∈ I} := by
  have hB₀ : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.background p.1) {p | p.1 ∈ I} :=
    C.background_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.jacobian p.1) {p | p.1 ∈ I} :=
    C.jacobian_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hT : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.curvature p.1) {p | p.1 ∈ I} :=
    C.curvature_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hp : ContDiffOn ℝ ∞ (fun p : ℝ × Z => D₁ p.2) {p | p.1 ∈ I} :=
    (D₁.contDiff.comp contDiff_snd).contDiffOn
  have hB : ContDiffOn ℝ ∞ (fun p : ℝ × Z => D₂ p.2) {p | p.1 ∈ I} :=
    (D₂.contDiff.comp contDiff_snd).contDiffOn
  let L : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
  exact L.contDiff.comp_contDiffOn (hB₀.add (contDiffOn_transformedHessianField hα hJ hT hp hB))

theorem DeformationFields.hessianField_value
    (C : DeformationFields r α I Φ B₀ f) (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    {t : ℝ} (ht : t ∈ I) (v : Z) (u : E → ℝ) (x : {x | r x ≤ 0})
    (hbij : Function.Bijective (fun y => Φ (t,y)))
    (hB₀ : ContDiffAt ℝ 2 B₀ (Φ (t,x))) (hu : ContDiffAt ℝ 2 u x)
    (hi : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) (Φ (t,x)))
    (hD₁ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (D₁ v) x = fderiv ℝ u x)
    (hD₂ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (D₂ v) x = fderiv ℝ (fderiv ℝ u) x) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField hα D₁ D₂ (t,v)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+u (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y)) (Φ (t,x)) := by
  have hinv : OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t (Φ (t,x)) = x := Function.leftInverse_invFun hbij.injective x
  have hu' : ContDiffAt ℝ 2 u (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t (Φ (t,x))) := by simpa only [hinv] using hu
  have hadd : fderiv ℝ (fderiv ℝ (fun y => B₀ y+u (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y))) (Φ (t,x)) =
      fderiv ℝ (fderiv ℝ B₀) (Φ (t,x)) +
        fderiv ℝ (fderiv ℝ (fun y => u (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y))) (Φ (t,x)) := by
    simpa only [Function.comp_def] using! second_fderiv_add_at hB₀ (hu'.comp _ hi)
  change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background t) x +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα (C.jacobian t)
        (C.curvature t) (D₁ v) (D₂ v)) x) (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  congr 1
  funext i j
  rw [hadd]
  simp only [add_apply,value_transformedHessianField,
    C.background_value t ht x,C.jacobian_value t ht x,C.curvature_value t ht x,hD₁,hD₂,
    OAI.Analysis.PDE.Dirichlet.inverseJacobian,OAI.Analysis.PDE.Dirichlet.inverseHessian]
  congr 1
  simpa only [hinv] using! (OAI.Analysis.PDE.Elliptic.second_fderiv_comp hu' hi
    (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)).symm

end OAI.Analysis.PDE.Schauder
