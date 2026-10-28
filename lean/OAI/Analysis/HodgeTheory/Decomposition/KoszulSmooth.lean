import OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Koszul Smooth -/

namespace OAI.Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions

noncomputable section

section

/-! Smooth dependence of the explicitly constructed metric connection on
the actual metric and its derivative. -/

open scoped ContDiff

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

local instance koszulBilinearNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance koszulBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem koszulFirstKind_smoothOn
    (T : D → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) {U : Set D}
    (hT : ContDiffOn ℝ ∞ T U) : ContDiffOn ℝ ∞ (fun x => KoszulConnection.Constructions.koszulFirstKind (T x)) U := by
  have hswap : ContDiffOn ℝ ∞ (fun x => (T x).flip) U :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp_contDiffOn hT
  have hcycle : ContDiffOn ℝ ∞ (fun x =>
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.comp (T x).flip) U :=
    contDiffOn_const.clm_comp hswap
  exact ((hT.add hswap).sub hcycle).const_smul (1 / 2 : ℝ)

theorem bilinearMetricSharp_smoothOn (B : D → E →L[ℝ] E →L[ℝ] ℝ) {U : Set D}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hpos : ∀ x ∈ U, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ContDiffOn ℝ ∞ (fun x => KoszulConnection.Constructions.bilinearMetricSharp (B x)) U :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.positive_bilinear_inverse_smoothOn B hU hB hpos).clm_comp contDiffOn_const

theorem koszulConnection_smoothOn
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (T : D → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) {U : Set D}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) (hT : ContDiffOn ℝ ∞ T U)
    (hpos : ∀ x ∈ U, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ContDiffOn ℝ ∞ (fun x => KoszulConnection.Constructions.koszulConnection (B x) (T x)) U := by
  have hsharp := bilinearMetricSharp_smoothOn B hU hB hpos
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  exact hsharp.clm_apply (((koszulFirstKind_smoothOn T hT).clm_apply
    (contDiffOn_const (c := u))).clm_apply (contDiffOn_const (c := v)))

end

/-! Differentiating the actual inverse metric in a metric-compatible
connection, with no assumed identity for inverse-metric derivatives. -/

open scoped ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem bilinearMetricSharp_derivative
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (u : E) (Γ : E →L[ℝ] E)
    (hΓ : ∀ v w, B x (Γ v) w + B x v (Γ w) = fderiv ℝ B x u v w)
    (α : E →L[ℝ] ℝ) :
    fderiv ℝ (fun y => KoszulConnection.Constructions.bilinearMetricSharp (B y) α) x u =
      -Γ (KoszulConnection.Constructions.bilinearMetricSharp (B x) α) - KoszulConnection.Constructions.bilinearMetricSharp (B x) (α.comp Γ) := by
  have hBd := (hB.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hS := ((bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := α))).contDiffAt (hU.mem_nhds hx)
  have hSd := hS.differentiableAt (by simp)
  apply KoszulConnection.Constructions.positive_bilinear_left_ext (B x) (hpos x hx)
  intro w
  have heq : (fun y => B y (KoszulConnection.Constructions.bilinearMetricSharp (B y) α) w) =ᶠ[𝓝 x] (fun _ => α w) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact KoszulConnection.Constructions.bilinearMetricSharp_pair (B y) (hpos y hy) α w
  have hz : fderiv ℝ (fun y => B y (KoszulConnection.Constructions.bilinearMetricSharp (B y) α) w) x u = 0 := by
    rw [heq.fderiv_eq, fderiv_const_apply]
    rfl
  have hder : fderiv ℝ (fun y => B y (KoszulConnection.Constructions.bilinearMetricSharp (B y) α) w) x u =
      fderiv ℝ B x u (KoszulConnection.Constructions.bilinearMetricSharp (B x) α) w +
        B x (fderiv ℝ (fun y => KoszulConnection.Constructions.bilinearMetricSharp (B y) α) x u) w := by
    rw [fderiv_clm_apply (hBd.clm_apply hSd) (differentiableAt_const w), fderiv_clm_apply hBd hSd]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  rw [hder] at hz
  have hmetric := hΓ (KoszulConnection.Constructions.bilinearMetricSharp (B x) α) w
  rw [KoszulConnection.Constructions.bilinearMetricSharp_pair (B x) (hpos x hx)] at hmetric
  rw [map_sub, map_neg, sub_apply, neg_apply, KoszulConnection.Constructions.bilinearMetricSharp_pair (B x) (hpos x hx)]
  change B x (fderiv ℝ (fun y => KoszulConnection.Constructions.bilinearMetricSharp (B y) α) x u) w =
    -B x (Γ (KoszulConnection.Constructions.bilinearMetricSharp (B x) α)) w - α (Γ w)
  linarith

end

end OAI.Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions
