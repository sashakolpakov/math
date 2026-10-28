import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatch
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.DriftJet

/-! All local Schauder jet bounds for data defined only on a closed half-patch.
The equation is assumed only on the open positive side. -/

noncomputable section
open Set Metric InnerProductSpace
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem uniform_closed_patch_jet_schauder {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α ell Λ N ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r < ρ / (Real.sqrt Λ+1) ∧ ∃ δ > 0,
      ∀ ε > 0, ∃ D > 0,
      ∀ (x₀ : EuclideanSpace ℝ (Fin m)), x₀ k = 0 →
      ∀ (a : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
        (A : OAI.Analysis.Normed.Function.Holder.HolderMap (closedCoordinateHalfPatch k x₀ ρ) (Matrix (Fin m) (Fin m) ℝ) α),
      ‖A‖ ≤ N → (∀ x : closedCoordinateHalfPatch k x₀ ρ, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a x) →
      (a x₀).PosDef →
      (∀ v : EuclideanSpace ℝ (Fin m), ell * ‖v‖^2 ≤
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (a x₀) v)) →
      (∀ v : EuclideanSpace ℝ (Fin m),
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (a x₀) v) ≤ Λ * ‖v‖^2) →
      ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        (∃ c > 0, ∀ z, L z k = c*z k) ∧
        ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
        ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 3 u →
        (∀ x ∈ ball x₀ ρ, x k = 0 → u x = 0) →
        ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ)
          (F : OAI.Analysis.Normed.Function.Holder.HolderMap (closedCoordinateHalfPatch k x₀ ρ) ℝ α),
        (∀ x : closedCoordinateHalfPatch k x₀ ρ, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = f x) →
        ∀ H M, 0 ≤ H → 0 ≤ M →
        (∀ x ∈ ball x₀ ρ, 0 ≤ x k → |u x| ≤ M) →
        (∀ x ∈ ball x₀ ρ, 0 < x k → OAI.Analysis.PDE.Schauder.nondivergenceOperator a u x = f x) →
        (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z * u (x₀ + L (r • z)))) x -
            fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z * u (x₀ + L (r • z)))) y‖ ≤
              H * ‖x-y‖^α) →
        (∀ x ∈ ball x₀ δ, 0 ≤ x k →
          |u x| ≤ M ∧ ‖fderiv ℝ u x‖ ≤ ε*H+D*(‖F‖+M) ∧
            ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε*H+D*(‖F‖+M)) ∧
        ∀ x ∈ ball x₀ δ, 0 ≤ x k → ∀ y ∈ ball x₀ δ, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖^α := by
  obtain ⟨r, hr, hrone, hrnear, δ, hδ, hcore⟩ :=
    OAI.Analysis.PDE.Schauder.uniform_boundary_local_jet_schauder_with_drift hm k hα hα1 hell hΛ hN
      (Nb := 0) le_rfl hρ
  refine ⟨r, hr, hrone, hrnear, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨D, hD, hcore⟩ := hcore ε hε
  refine ⟨D, hD, ?_⟩
  intro x₀ hx₀ a A hAn hAval hpos hlo hhi
  have hne := nonempty_closedCoordinateHalfPatch k x₀ hρ.le hx₀
  have hc := (isCompact_closedCoordinateHalfPatch k x₀ ρ).isComplete
  have hconv := convex_closedCoordinateHalfPatch k x₀ ρ
  obtain ⟨A', hA', hA'n⟩ := exists_convex_holder_extension hne hc hconv hα.le A
  have hAe (x) (hx : x ∈ closedCoordinateHalfPatch k x₀ ρ) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value A' x = a x := (hA' ⟨x, hx⟩).trans (hAval ⟨x, hx⟩)
  have hx₀K : x₀ ∈ closedCoordinateHalfPatch k x₀ ρ :=
    ⟨mem_closedBall_self hρ.le, by simp only [Set.mem_ofPred_eq, hx₀, le_refl]⟩
  obtain ⟨L, hLn, hL, hLi, hlocal⟩ := hcore A' (hA'n.trans hAn) x₀ hx₀
    (by simpa only [hAe x₀ hx₀K] using hpos)
    (by simpa only [hAe x₀ hx₀K] using hlo)
    (by simpa only [hAe x₀ hx₀K] using hhi)
  refine ⟨L, hLn, hL, hLi, ?_⟩
  intro u hu hz f F hFval H M hH hM hb he hh
  obtain ⟨F', hF', hF'n⟩ := exists_convex_holder_extension hne hc hconv hα.le F
  have hFe (x) (hx : x ∈ closedCoordinateHalfPatch k x₀ ρ) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value F' x = f x := (hF' ⟨x, hx⟩).trans (hFval ⟨x, hx⟩)
  have he' : ∀ z ∈ ball x₀ ρ, 0 < z k →
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') u z = OAI.Analysis.Normed.Function.Holder.HolderMap.value F' z := by
    intro z hz hzk
    have hzK : z ∈ closedCoordinateHalfPatch k x₀ ρ := ⟨ball_subset_closedBall hz, hzk.le⟩
    simpa only [OAI.Analysis.PDE.Schauder.nondivergenceOperator, hAe z hzK, hFe z hzK] using he z hz hzk
  have heclosed := equation_on_nonnegative_coordinate_patch k isOpen_ball
    (continuous_nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A').continuous
      (hu.of_le (by norm_num))) (OAI.Analysis.Normed.Function.Holder.HolderMap.value F').continuous he'
  have hzero : ‖(0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) α)‖ ≤ 0 := by simp
  obtain ⟨hjet, hholder⟩ := hlocal 0 hzero u hu hz F' H M hH hM hb (by
    intro x hx hxk
    change OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') u x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value F' x + fderiv ℝ u x 0
    simpa only [map_zero, add_zero] using heclosed x hx hxk) hh
  have hmore : ε*H+D*(‖F'‖+M) ≤ ε*H+D*(‖F‖+M) := by
    gcongr
  constructor
  · intro x hx hxk
    obtain ⟨hv, hd, hdd⟩ := hjet x hx hxk
    exact ⟨hv, hd.trans hmore, hdd.trans hmore⟩
  · intro x hx hxk y hy hyk
    exact (hholder x hx hxk y hy hyk).trans
      (mul_le_mul_of_nonneg_right hmore (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Elliptic
