import OAI.LieTheory.Semisimple.Algebra
import OAI.LieTheory.Semisimple.Differential
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! # Character Triviality Kills -/

namespace OAI.LieTheory.Semisimple.CharacterTrivialityKills.Constructions

noncomputable section

/-! A smooth complex-valued character kills Lie brackets under differentiation. -/

open Set Filter VectorField
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (𝓘(ℝ, E)) ∞ G]

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] in
theorem mfderiv_character_invariant (φ : G →* ℂ)
    (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) φ)
    (g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mvfderiv (𝓘(ℝ, E)) φ g (mulInvariantVectorField v g) =
      φ g * (mvfderiv (𝓘(ℝ, E)) φ 1 v : ℂ) := by
  let A : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) (φ g)
  have heq : (φ ∘ (fun x : G => g * x)) = A ∘ φ := by
    funext x
    exact φ.map_mul g x
  have hleft : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1 :=
    (contMDiff_mul_left (n := ∞)).mdifferentiableAt (by simp)
  have hchain := Differential.Constructions.CharacterTriviality.vectorDerivative_comp (fun x : G => g * x) (φ : G → ℂ)
    (1 : G) (hφ (g * 1)) hleft
  rw [heq, Differential.Constructions.CharacterTriviality.vectorDerivative_clm A φ 1 (hφ 1)] at hchain
  erw [mul_one] at hchain
  have h := congrArg (fun T : E →L[ℝ] ℂ => T v) hchain
  change φ g * mvfderiv (𝓘(ℝ, E)) φ 1 v =
    mvfderiv (𝓘(ℝ, E)) φ g (mulInvariantVectorField v g) at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem character_derivative_kills_brackets (φ : G →* ℂ)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ φ)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mvfderiv (𝓘(ℝ, E)) φ 1 ⁅v, w⁆ = 0 := by
  let e := extChartAt (𝓘(ℝ, E)) (1 : G)
  let k : E → ℂ := φ ∘ e.symm
  let V : E → E := mpullback (𝓘(ℝ, E)) (𝓘(ℝ, E)) e.symm (mulInvariantVectorField v)
  let W : E → E := mpullback (𝓘(ℝ, E)) (𝓘(ℝ, E)) e.symm (mulInvariantVectorField w)
  let a : ℂ := mvfderiv (𝓘(ℝ, E)) φ 1 v
  let b : ℂ := mvfderiv (𝓘(ℝ, E)) φ 1 w
  have he (y : E) (hy : y ∈ e.target) :
      ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ e.symm y := by
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] using
      contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, E)) (n := ∞) (1 : G) hy
  have hk (y : E) (hy : y ∈ e.target) : ContDiffAt ℝ ∞ k y :=
    (hφ.contMDiffAt.comp y (he y hy)).contDiffAt
  have hcoord (u : GroupLieAlgebra (𝓘(ℝ, E)) G) (y : E) (hy : y ∈ e.target) :
      fderiv ℝ k y
        (mpullback (𝓘(ℝ, E)) (𝓘(ℝ, E)) e.symm (mulInvariantVectorField u) y) =
        k y * (mvfderiv (𝓘(ℝ, E)) φ 1 u : ℂ) := by
    have hi : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) e.symm y).IsInvertible := by
      simpa only [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hy
    change fderiv ℝ (φ ∘ e.symm) y _ = _
    erw [← mfderiv_eq_fderiv, mfderiv_comp y (hφ.mdifferentiable (by simp) _)
      ((he y hy).mdifferentiableAt (by simp)), ContinuousLinearMap.comp_apply,
      mpullback_apply, hi.self_apply_inverse]
    exact mfderiv_character_invariant φ (hφ.mdifferentiable (by simp)) (e.symm y) u
  have hV : DifferentiableAt ℝ V (e 1) := by
    have h := (mdifferentiableAt_mulInvariantVectorField (I := 𝓘(ℝ, E)) v (g := (1 : G))).mdifferentiableWithinAt (s := univ)
    have h' := h.differentiableWithinAt_mpullbackWithin_vectorField
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, preimage_univ, univ_inter,
      mpullbackWithin_univ, differentiableWithinAt_univ] using h'
  have hW : DifferentiableAt ℝ W (e 1) := by
    have h := (mdifferentiableAt_mulInvariantVectorField (I := 𝓘(ℝ, E)) w (g := (1 : G))).mdifferentiableWithinAt (s := univ)
    have h' := h.differentiableWithinAt_mpullbackWithin_vectorField
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, preimage_univ, univ_inter,
      mpullbackWithin_univ, differentiableWithinAt_univ] using h'
  have hne : e.target ∈ 𝓝 (e 1) :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (1 : G)).mem_nhds (mem_extChartAt_target 1)
  have heqV : (fun y => fderiv ℝ k y (V y)) =ᶠ[𝓝 (e 1)] (fun y => k y * a) := by
    filter_upwards [hne] with y hy using hcoord v y hy
  have heqW : (fun y => fderiv ℝ k y (W y)) =ᶠ[𝓝 (e 1)] (fun y => k y * b) := by
    filter_upwards [hne] with y hy using hcoord w y hy
  have hbr := fderiv_apply_lieBracket (hk (e 1) (mem_extChartAt_target 1))
    (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top) hW hV
  rw [heqW.fderiv_eq, heqV.fderiv_eq,
    fderiv_mul_const ((hk (e 1) (mem_extChartAt_target 1)).differentiableAt (by simp)),
    fderiv_mul_const ((hk (e 1) (mem_extChartAt_target 1)).differentiableAt (by simp))] at hbr
  have hz : fderiv ℝ k (e 1) (lieBracket ℝ V W (e 1)) = 0 := by
    rw [hbr]
    change b * fderiv ℝ k (e 1) (V (e 1)) - a * fderiv ℝ k (e 1) (W (e 1)) = 0
    rw [hcoord v _ (mem_extChartAt_target 1), hcoord w _ (mem_extChartAt_target 1)]
    change b * (k (e 1) * a) - a * (k (e 1) * b) = 0
    ring
  have hd : fderiv ℝ k (e 1) = mvfderiv (𝓘(ℝ, E)) φ 1 := by
    change fderiv ℝ (φ ∘ e.symm) (e 1) = _
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e 1) (hφ.mdifferentiable (by simp) _)
      ((he (e 1) (mem_extChartAt_target 1)).mdifferentiableAt (by simp))]
    have hid := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := (1 : G))
    rw [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] at hid
    erw [hid, ContinuousLinearMap.comp_id, e.left_inv (mem_extChartAt_source 1)]
    rfl
  rw [hd] at hz
  simp +instances only [GroupLieAlgebra.bracket_def, mlieBracket, mlieBracketWithin_apply,
    mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id,
    ModelWithCorners.Boundaryless.range_eq_univ, preimage_univ, univ_inter,
    mpullbackWithin_univ, lieBracketWithin_univ]
  change mvfderiv (𝓘(ℝ, E)) φ 1 (lieBracket (E := E) ℝ V W (e 1)) = 0
  exact hz

end

end OAI.LieTheory.Semisimple.CharacterTrivialityKills.Constructions
