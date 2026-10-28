import OAI.Analysis.Normed.Function.Holder.Banach.Polynomial
import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule

/-! Polynomial action of the first two derivatives of a coordinate map
on an unknown function's first two jets. All fields are evaluated at the
same point; no composition operator on a rough Hölder space is used. -/

noncomputable section
open scoped ContDiff
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α : ℝ}
local notation "D" => E →L[ℝ] ℝ
local notation "A" => E →L[ℝ] E
local notation "H" => E →L[ℝ] E →L[ℝ] ℝ
local notation "K" => E →L[ℝ] E →L[ℝ] E
local instance transformedDualGroup : NormedAddCommGroup D := inferInstance
local instance transformedDualSpace : NormedSpace ℝ D := inferInstance
local instance transformedEndGroup : NormedAddCommGroup A := inferInstance
local instance transformedEndSpace : NormedSpace ℝ A := inferInstance
local instance transformedSecondGroup : NormedAddCommGroup H := inferInstance
local instance transformedSecondSpace : NormedSpace ℝ H := inferInstance
local instance transformedMapSecondGroup : NormedAddCommGroup K := inferInstance
local instance transformedMapSecondSpace : NormedSpace ℝ K := inferInstance

def transformedHessianField (hα : 0 ≤ α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X A α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X K α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X D α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X H α) : OAI.Analysis.Normed.Function.Holder.HolderMap X H α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.compL ℝ E D D)
    (OAI.Analysis.Normed.Function.Holder.HolderMap.map (ContinuousLinearMap.compL ℝ E E ℝ).flip J)
    (OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.compL ℝ E E D) B J) +
  OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.compL ℝ E A D)
    (OAI.Analysis.Normed.Function.Holder.HolderMap.map (ContinuousLinearMap.compL ℝ E E ℝ) p) T

@[simp] theorem value_transformedHessianField (hα : 0 ≤ α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X A α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X K α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X D α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X H α) (x : X) (v w : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα J T p B) x v w =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value B x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x w) +
        OAI.Analysis.Normed.Function.Holder.HolderMap.value p x (OAI.Analysis.Normed.Function.Holder.HolderMap.value T x v w) := rfl

theorem contDiff_transformedHessianField
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ∞ω}
    (hα : 0 ≤ α) {J : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X A α} {T : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X K α}
    {p : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X D α} {B : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X H α}
    (hJ : ContDiff ℝ q J) (hT : ContDiff ℝ q T)
    (hp : ContDiff ℝ q p) (hB : ContDiff ℝ q B) :
    ContDiff ℝ q (fun y => transformedHessianField hα (J y) (T y) (p y) (B y)) := by
  have hright := (OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.compL ℝ E E D) q).comp (hB.prodMk hJ)
  have hleft := (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (X := X) (α := α) (ContinuousLinearMap.compL ℝ E E ℝ).flip).contDiff.comp hJ
  have hprincipal := (OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.compL ℝ E D D) q).comp (hleft.prodMk hright)
  have hpost := (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (X := X) (α := α) (ContinuousLinearMap.compL ℝ E E ℝ)).contDiff.comp hp
  have hcurvature := (OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.compL ℝ E A D) q).comp (hpost.prodMk hT)
  exact hprincipal.add hcurvature

theorem transformedHessianField_identity (hα : 0 ≤ α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X D α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X H α) :
    transformedHessianField hα (OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E))
      (OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0) p B = B := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  ext v w
  simp only [value_transformedHessianField,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant,
    ContinuousLinearMap.id_apply,zero_apply,map_zero,add_zero]

theorem contDiffOn_transformedHessianField
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {q : ℕ∞ω} {S : Set Y}
    (hα : 0 ≤ α) {J : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X A α} {T : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X K α}
    {p : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X D α} {B : Y → OAI.Analysis.Normed.Function.Holder.HolderMap X H α}
    (hJ : ContDiffOn ℝ q J S) (hT : ContDiffOn ℝ q T S)
    (hp : ContDiffOn ℝ q p S) (hB : ContDiffOn ℝ q B S) :
    ContDiffOn ℝ q (fun y => transformedHessianField hα (J y) (T y) (p y) (B y)) S := by
  have hright := (OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.compL ℝ E E D) q).comp_contDiffOn (hB.prodMk hJ)
  have hleft := (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (X := X) (α := α) (ContinuousLinearMap.compL ℝ E E ℝ).flip).contDiff.comp_contDiffOn hJ
  have hprincipal := (OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.compL ℝ E D D) q).comp_contDiffOn (hleft.prodMk hright)
  have hpost := (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (X := X) (α := α) (ContinuousLinearMap.compL ℝ E E ℝ)).contDiff.comp_contDiffOn hp
  have hcurvature := (OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_bilinear (X := X) hα (ContinuousLinearMap.compL ℝ E A D) q).comp_contDiffOn (hpost.prodMk hT)
  exact hprincipal.add hcurvature

end OAI.Analysis.PDE.Schauder
