import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftAssembly
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftGeometry
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftPullback
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierThree

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "P" => ℝ × E
local instance dataFirstGroup : NormedAddCommGroup (P →L[ℝ] ℝ) := inferInstance
local instance dataFirstSpace : NormedSpace ℝ (P →L[ℝ] ℝ) := inferInstance
local instance dataSecondGroup : NormedAddCommGroup (P →L[ℝ] P →L[ℝ] ℝ) := inferInstance
local instance dataSecondSpace : NormedSpace ℝ (P →L[ℝ] P →L[ℝ] ℝ) := inferInstance
local instance dataThirdGroup : NormedAddCommGroup (P →L[ℝ] P →L[ℝ] P →L[ℝ] ℝ) := inferInstance
local instance dataThirdSpace : NormedSpace ℝ (P →L[ℝ] P →L[ℝ] P →L[ℝ] ℝ) := inferInstance

theorem regularizedTrace_three_derivatives (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (p : P) (hp : p.1 ≠ 0) :
    let S := fun q : P ↦ regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) q.1 q.2
    HasFDerivAt S (fderiv ℝ S p) p ∧
      HasFDerivAt (fderiv ℝ S) (fderiv ℝ (fderiv ℝ S) p) p ∧
      HasFDerivAt (fderiv ℝ (fderiv ℝ S)) (fderiv ℝ (fderiv ℝ (fderiv ℝ S)) p) p := by
  dsimp only
  have hs := contDiffAt_regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) (OAI.Analysis.Normed.Function.Holder.HolderMap.value h).continuous p hp
  have hs1 := hs.fderiv_right (m := 2) (by norm_num)
  have hs2 := hs1.fderiv_right (m := 1) (by norm_num)
  exact ⟨(hs.differentiableAt (by simp)).hasFDerivAt,
    (hs1.differentiableAt (by norm_num)).hasFDerivAt,
    (hs2.differentiableAt (by norm_num)).hasFDerivAt⟩

theorem exists_boundaryLiftRegularization (hα : 0 ≤ α) (e : E) (he : ‖e‖ = 1)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    ∃ a : BoundaryLiftRegularization (innerSL ℝ e) α,
      a.s = (fun x ↦ regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) (inner ℝ e x) (normalProjection e x)) ∧
      a.b = (fun x ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value h (normalProjection e x)) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedTrace_three_derivative_bound m hα
  let L := normalRegularizationMap e
  let S := fun q : P ↦ regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) q.1 q.2
  let D := fun x ↦ precomposeJet L (fderiv ℝ S (L x))
  let DD := fun x ↦ precomposeSecondJet L (fderiv ℝ (fderiv ℝ S) (L x))
  let DDD := fun x ↦ precomposeThirdJet L (fderiv ℝ (fderiv ℝ (fderiv ℝ S)) (L x))
  have hL : ‖L‖ ≤ 1 := norm_normalRegularizationMap_le e he
  have hder (x : E) (hx : (innerSL ℝ e) x ≠ 0) :=
    regularizedTrace_three_derivatives h (L x) hx
  refine ⟨{
    s := fun x ↦ S (L x)
    b := fun x ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value h (normalProjection e x)
    D := D
    DD := DD
    DDD := DDD
    M := ‖h‖
    H := ‖h‖
    C0 := ‖h‖
    C1 := C * ‖h‖
    C2 := C * ‖h‖
    C3 := C * ‖h‖
    nonneg_M := norm_nonneg h
    nonneg_H := norm_nonneg h
    nonneg_C0 := norm_nonneg h
    nonneg_C1 := mul_nonneg hC.le (norm_nonneg h)
    nonneg_C2 := mul_nonneg hC.le (norm_nonneg h)
    nonneg_C3 := mul_nonneg hC.le (norm_nonneg h)
    bounded := fun x ↦ norm_regularizedTrace_le h _ _
    holder := ?_
    error := fun x ↦ norm_regularizedTrace_sub_le hα h _ _
    deriv_s := ?_
    deriv_D := ?_
    deriv_DD := ?_
    bound_D := ?_
    bound_DD := ?_
    bound_DDD := ?_
  }, rfl, rfl⟩
  · intro x y
    have hp : ‖normalProjection e x - normalProjection e y‖ ≤ ‖x - y‖ := by
      change ‖normalProjectionMap e x - normalProjectionMap e y‖ ≤ _
      rw [← map_sub]
      exact norm_normalProjection_le e he (x - y)
    have hhb := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le h (normalProjection e x) (normalProjection e y)
    simp only [Real.norm_eq_abs, dist_eq_norm] at hhb
    exact hhb.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hp hα) (norm_nonneg h))
  · intro x hx
    exact (hder x hx).1.comp x L.hasFDerivAt
  · intro x hx
    exact hasFDerivAt_precomposeFirstJet L (fderiv ℝ S) (fderiv ℝ (fderiv ℝ S)) x
      (hder x hx).2.1
  · intro x hx
    exact hasFDerivAt_precomposeSecondJet L (fderiv ℝ (fderiv ℝ S))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ S))) x (hder x hx).2.2
  · intro x hx
    exact (norm_precomposeJet_apply L hL _).trans (hb h (L x) hx).1
  · intro x hx
    exact (norm_precomposeSecondJet_apply L hL _).trans (hb h (L x) hx).2.1
  · intro x hx
    exact (norm_precomposeThirdJet L hL _).trans (hb h (L x) hx).2.2

end OAI.Analysis.PDE.Schauder
