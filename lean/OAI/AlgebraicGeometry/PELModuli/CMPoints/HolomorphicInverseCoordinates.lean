import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.Basic

/-! # Holomorphic Inverse Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicInverseCoordinates

noncomputable section

section

/-! Local holomorphic inversion with an actual continuous inverse.
The joint base-and-fiber derivative is computed from the zero section
and the identity vertical derivative. -/

open Set Filter
open scoped _root_.Topology ContDiff

theorem joint_map_hasFDerivAt_id
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (g : P × V → V) (p₀ : P) (hg : DifferentiableAt ℂ g (p₀, 0))
    (hzero : ∀ᶠ p in 𝓝 p₀, g (p, 0) = 0)
    (hvertical : HasFDerivAt (fun v => g (p₀, v)) (ContinuousLinearMap.id ℂ V) 0) :
    HasFDerivAt (fun q : P × V => (q.1, g q)) (ContinuousLinearMap.id ℂ (P × V)) (p₀, 0) := by
  let d := fderiv ℂ g (p₀, 0)
  have hl : HasFDerivAt (fun p => g (p, 0))
      (d.comp (ContinuousLinearMap.inl ℂ P V)) p₀ :=
    hg.hasFDerivAt.comp p₀ ((hasFDerivAt_id p₀).prodMk (hasFDerivAt_const (0 : V) p₀))
  have hl0 : HasFDerivAt (fun p => g (p, 0)) (0 : P →L[ℂ] V) p₀ :=
    (hasFDerivAt_const (0 : V) p₀).congr_of_eventuallyEq hzero
  have hr : HasFDerivAt (fun v => g (p₀, v))
      (d.comp (ContinuousLinearMap.inr ℂ P V)) 0 :=
    hg.hasFDerivAt.comp 0 ((hasFDerivAt_const p₀ (0 : V)).prodMk (hasFDerivAt_id 0))
  have hdl := hl.unique hl0
  have hdr := hr.unique hvertical
  have hd : d = ContinuousLinearMap.snd ℂ P V := by
    apply ContinuousLinearMap.ext
    intro x
    have h₁ : d (x.1, 0) = 0 := congrArg (fun T : P →L[ℂ] V => T x.1) hdl
    have h₂ : d (0, x.2) = x.2 := congrArg (fun T : V →L[ℂ] V => T x.2) hdr
    change d x = x.2
    calc
      d x = d (x.1, 0) + d (0, x.2) := by
        rw [← map_add]
        congr 1
        exact (Prod.ext (add_zero x.1) (zero_add x.2)).symm
      _ = x.2 := by rw [h₁, h₂, zero_add]
  have h := (hasFDerivAt_fst (𝕜 := ℂ)).prodMk hg.hasFDerivAt
  apply h.congr_fderiv
  change (ContinuousLinearMap.fst ℂ P V).prod d = _
  rw [hd]
  rfl

theorem contDiffAt_actual_local_inverse
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (f g : V → V) (a : V) (hf : ContDiffAt ℂ 1 f a)
    (hdf : HasFDerivAt f (ContinuousLinearMap.id ℂ V) a)
    (hfa : f a = a) (hga : g a = a) (hg : ContinuousAt g a)
    (hinv : ∀ᶠ y in 𝓝 a, f (g y) = y) : ContDiffAt ℂ 1 g a := by
  let e := hf.toOpenPartialHomeomorph f (f' := ContinuousLinearEquiv.refl ℂ V) hdf (by norm_num)
  have ha : a ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℂ V) hdf (by norm_num)
  have hmem : ∀ᶠ y in 𝓝 a, g y ∈ e.source := by
    apply hg.preimage_mem_nhds
    rw [hga]
    exact e.open_source.mem_nhds ha
  have heq : g =ᶠ[𝓝 a] e.symm := by
    filter_upwards [hinv, hmem] with y hy hys
    have h := e.left_inv hys
    change e.symm (f (g y)) = g y at h
    rw [hy] at h
    exact h.symm
  have h := hf.to_localInverse (f' := ContinuousLinearEquiv.refl ℂ V) hdf (by norm_num)
  change ContDiffAt ℂ 1 e.symm (f a) at h
  rw [hfa] at h
  exact h.congr_of_eventuallyEq heq

theorem exists_open_holomorphic_actual_inverse
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (f g : V → V) (a : V) (hf : ContDiffAt ℂ 1 f a)
    (hdf : HasFDerivAt f (ContinuousLinearMap.id ℂ V) a)
    (hfa : f a = a) (hga : g a = a) (hg : ContinuousAt g a)
    (hinv : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    ∃ U : Set V, IsOpen U ∧ a ∈ U ∧ DifferentiableOn ℂ g U := by
  have h := (contDiffAt_actual_local_inverse f g a hf hdf hfa hga hg hinv).eventually (by norm_num)
  obtain ⟨U, hUsub, hU, ha⟩ := mem_nhds_iff.mp h
  refine ⟨U, hU, ha, fun y hy => ?_⟩
  have hcy : ContDiffAt ℂ 1 g y := hUsub hy
  exact (hcy.differentiableAt (by norm_num)).differentiableWithinAt

end

/-! Joint holomorphic dependence of a continuous inverse in relative
coordinates, using the actual real vertical derivative at the identity. -/

open Set Filter
open scoped _root_.Topology ContDiff

theorem complex_hasFDerivAt_id_of_real
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [IsScalarTower ℝ ℂ V] (g : V → V) (a : V) (hg : DifferentiableAt ℂ g a)
    (hr : HasFDerivAt g (ContinuousLinearMap.id ℝ V) a) :
    HasFDerivAt g (ContinuousLinearMap.id ℂ V) a := by
  apply hg.hasFDerivAt.congr_fderiv
  apply (ContinuousLinearMap.restrictScalarsIsometry ℂ V V ℝ ℝ).injective
  exact (hg.hasFDerivAt.restrictScalars ℝ).unique hr

theorem exists_open_holomorphic_inverse_coordinates
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [IsScalarTower ℝ ℂ V] [CompleteSpace V]
    (f g : P × V → V) (p₀ : P) (hg : ContDiffAt ℂ 1 g (p₀, 0))
    (hzero : ∀ᶠ p in 𝓝 p₀, g (p, 0) = 0)
    (hvertical : HasFDerivAt (fun v => g (p₀, v)) (ContinuousLinearMap.id ℝ V) 0)
    (hf : ContinuousAt f (p₀, 0)) (hfzero : f (p₀, 0) = 0)
    (hinv : ∀ᶠ q in 𝓝 (p₀, (0 : V)), g (q.1, f q) = q.2) :
    ∃ U : Set (P × V), IsOpen U ∧ (p₀, (0 : V)) ∈ U ∧ DifferentiableOn ℂ f U := by
  have hgd : DifferentiableAt ℂ g (p₀, 0) := hg.differentiableAt (by norm_num)
  have hvd : DifferentiableAt ℂ (fun v => g (p₀, v)) 0 :=
    hgd.comp 0 ((differentiableAt_const p₀).prodMk differentiableAt_id)
  have hvc := complex_hasFDerivAt_id_of_real (fun v => g (p₀, v)) 0 hvd hvertical
  let F : P × V → P × V := fun q => (q.1, g q)
  let G : P × V → P × V := fun q => (q.1, f q)
  have hF : ContDiffAt ℂ 1 F (p₀, 0) := contDiffAt_fst.prodMk hg
  have hFd : HasFDerivAt F (ContinuousLinearMap.id ℂ (P × V)) (p₀, 0) :=
    joint_map_hasFDerivAt_id g p₀ hgd hzero hvc
  have hFzero : F (p₀, 0) = (p₀, 0) := Prod.ext rfl hzero.self_of_nhds
  have hGzero : G (p₀, 0) = (p₀, 0) := Prod.ext rfl hfzero
  have hG : ContinuousAt G (p₀, 0) := continuousAt_fst.prodMk hf
  have hFG : ∀ᶠ q in 𝓝 (p₀, (0 : V)), F (G q) = q :=
    hinv.mono (fun q hq => Prod.ext rfl hq)
  obtain ⟨U, hU, hpU, hGU⟩ := exists_open_holomorphic_actual_inverse F G (p₀, 0)
    hF hFd hFzero hGzero hG hFG
  exact ⟨U, hU, hpU, hGU.snd⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicInverseCoordinates
