import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Fields
import OAI.Analysis.PDE.Schauder.Calculus.TransformedBackground

open Set
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
variable {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
local instance deformationDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance deformationDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance deformationEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance deformationEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance deformationSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance deformationSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance deformationMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance deformationMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def DeformationFields.mooreOperator (C : DeformationFields r α I Φ B₀ f) (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (p : ℝ × Z) : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ α :=
  transformedBackgroundMooreField hα (C.background p.1) (C.jacobian p.1)
    (C.curvature p.1) (D₁ p.2) (D₂ p.2) - C.source p.1

theorem DeformationFields.contDiffOn_mooreOperator
    (C : DeformationFields r α I Φ B₀ f) (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) :
    ContDiffOn ℝ ∞ (C.mooreOperator hα D₁ D₂) {p | p.1 ∈ I} := by
  have hB₀ : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.background p.1) {p | p.1 ∈ I} :=
    C.background_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hJ : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.jacobian p.1) {p | p.1 ∈ I} :=
    C.jacobian_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hT : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.curvature p.1) {p | p.1 ∈ I} :=
    C.curvature_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × Z => C.source p.1) {p | p.1 ∈ I} :=
    C.source_smooth.comp contDiffOn_fst (fun p hp => hp)
  have hp : ContDiffOn ℝ ∞ (fun p : ℝ × Z => D₁ p.2) {p | p.1 ∈ I} :=
    (D₁.contDiff.comp contDiff_snd).contDiffOn
  have hB : ContDiffOn ℝ ∞ (fun p : ℝ × Z => D₂ p.2) {p | p.1 ∈ I} :=
    (D₂.contDiff.comp contDiff_snd).contDiffOn
  exact (contDiffOn_transformedBackgroundMooreField hα hB₀ hJ hT hp hB).sub hF

theorem DeformationFields.mooreOperator_value
    (C : DeformationFields r α I Φ B₀ f) (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    {t : ℝ} (ht : t ∈ I) (v : Z) (u : E → ℝ) (x : {x | r x ≤ 0})
    (hbij : Function.Bijective (fun y => Φ (t,y)))
    (hB₀ : ContDiffAt ℝ 2 B₀ (Φ (t,x))) (hu : ContDiffAt ℝ 2 u x)
    (hi : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) (Φ (t,x)))
    (hD₁ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (D₁ v) x = fderiv ℝ u x)
    (hD₂ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (D₂ v) x = fderiv ℝ (fderiv ℝ u) x) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.mooreOperator hα D₁ D₂ (t,v)) x =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
        (fun y => B₀ y+u (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t y)) (Φ (t,x))) - f (Φ (t,x)) := by
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα (C.background t)
    (C.jacobian t) (C.curvature t) (D₁ v) (D₂ v)) x - OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source t) x = _
  rw [C.source_value t ht x]
  congr 1
  apply transformedBackgroundMooreField_eq_composition hα _ _ _ _ _ B₀ u
    (OAI.Analysis.PDE.Dirichlet.inverseFamily Φ t) x x (Φ (t,x)) hB₀ hu hi
  · exact Function.leftInverse_invFun hbij.injective x
  · exact C.background_value t ht x
  · exact C.jacobian_value t ht x
  · exact C.curvature_value t ht x
  · exact hD₁
  · exact hD₂

end OAI.Analysis.PDE.Schauder
