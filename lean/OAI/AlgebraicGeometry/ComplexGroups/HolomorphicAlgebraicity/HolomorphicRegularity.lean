import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Holomorphic Regularity -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicRegularity.Constructions.Regularity

noncomputable section

/-!
# Cauchy formulas for regularity of finite-dimensional holomorphic maps

Local inverse charts require continuity of derivatives. The ingredients here
express directional derivatives as circle integrals and prove continuity of
circle integrals with respect to a finite-dimensional parameter.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology Real BigOperators ContDiff

/-- A circle integral depends continuously on a parameter when its integrand
is continuous on a neighborhood times the circle. -/
theorem continuousAt_circleIntegral {n : ℕ}
    {F : (Fin n → ℂ) → ℂ → ℂ} {U : Set (Fin n → ℂ)}
    {x : Fin n → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hU : IsOpen U) (hx : x ∈ U)
    (hF : ContinuousOn (fun p : (Fin n → ℂ) × ℂ => F p.1 p.2)
      (U ×ˢ sphere c R)) :
    ContinuousAt (fun y => ∮ z in C(c, R), F y z) x := by
  let K := sphere c R
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sphere c R)
  let family : (Fin n → ℂ) → K → ℂ := fun y z => F y z
  have hfamily : ContinuousOn (Function.uncurry family) (U ×ˢ univ) := by
    apply hF.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1, p.2.property⟩
  have huniform : TendstoUniformly family (family x) (𝓝 x) :=
    ContinuousOn.tendstoUniformly (hU.mem_nhds hx) hfamily
  have huniformOn : TendstoUniformlyOn F (F x) (𝓝 x) (sphere c R) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr huniform
  have hcontinuous : ∀ᶠ y in 𝓝 x, ContinuousOn (F y) (sphere c R) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hy, hz⟩)
  exact huniformOn.tendsto_circleIntegral_of_continuousOn hR hcontinuous

/-- Cauchy's formula computes a directional derivative using a disk in the
holomorphy domain. -/
theorem fderiv_apply_eq_circleIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (x v : E) {R : ℝ} (hR : 0 < R)
    (hball : ∀ z ∈ closedBall (0 : ℂ) R, x + z • v ∈ U) :
    fderiv ℂ f x v = (2 * π * I : ℂ)⁻¹ *
      ∮ z in C(0, R), (z ^ 2)⁻¹ * f (x + z • v) := by
  have hx : x ∈ U := by
    simpa only [zero_smul, add_zero] using hball 0 (mem_closedBall_self hR.le)
  have hline : Differentiable ℂ (fun z : ℂ => x + z • v) :=
    (differentiable_const x).add (differentiable_id.smul_const v)
  have hlineDeriv : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
    simpa only [id_eq, zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℂ) x).add ((hasDerivAt_id (0 : ℂ)).smul_const v)
  have hcomp : HasDerivAt (fun z : ℂ => f (x + z • v)) (fderiv ℂ f x v) 0 := by
    exact (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hlineDeriv (by simp)
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => f (x + z • v)) (closedBall 0 R) :=
    hf.comp hline.differentiableOn hball
  have hformula := hdiff.deriv_eq_smul_circleIntegral hR
  rw [hcomp.deriv] at hformula
  have hformula' : (∮ z in C(0, R), (z ^ 2)⁻¹ * f (x + z • v)) =
      (2 * π * I : ℂ) * fderiv ℂ f x v := by
    simpa only [sub_zero, one_div, smul_eq_mul] using hformula
  rw [hformula', ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- An open neighborhood contains a uniform family of small translated disks
in any fixed complex direction. -/
theorem exists_disk_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) (v : E) :
    ∃ R : ℝ, 0 < R ∧ ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ closedBall (0 : ℂ) R, y + z • v ∈ U := by
  have hline : Continuous (fun z : ℂ => x + z • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun z : ℂ => x + z • v) ⁻¹' U ∈ 𝓝 0 :=
    (hU.preimage hline).mem_nhds (by simpa only [mem_preimage, zero_smul, add_zero] using hx)
  obtain ⟨R, hR, hball⟩ := nhds_basis_closedBall.mem_iff.mp hpre
  have hmap : Continuous (fun p : E × ℂ => p.1 + p.2 • v) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hp : ({x} : Set E) ×ˢ closedBall (0 : ℂ) R ⊆
      (fun p : E × ℂ => p.1 + p.2 • v) ⁻¹' U := by
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    rcases mem_singleton_iff.mp hy with rfl
    exact hball hz
  obtain ⟨V, W, hV, _, hxV, hRW, hVW⟩ := generalized_tube_lemma
    isCompact_singleton (isCompact_closedBall (0 : ℂ) R) (hU.preimage hmap) hp
  exact ⟨R, hR, V, hV, hxV (mem_singleton x),
    fun y hy z hz => hVW (show (y, z) ∈ V ×ˢ W from ⟨hy, hRW hz⟩)⟩

/-- The Cauchy formula makes every fixed directional derivative continuous
on an open holomorphy domain. -/
theorem continuousAt_fderiv_apply {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : Fin n → ℂ} (hx : x ∈ U) (v : Fin n → ℂ) :
    ContinuousAt (fun y => fderiv ℂ f y v) x := by
  obtain ⟨R, hR, V, hV, hxV, hball⟩ := exists_disk_neighborhood hU hx v
  have hmap : Continuous (fun p : (Fin n → ℂ) × ℂ => p.1 + p.2 • v) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hvalue : ContinuousOn (fun p : (Fin n → ℂ) × ℂ => f (p.1 + p.2 • v))
      (V ×ˢ sphere (0 : ℂ) R) :=
    hf.continuousOn.comp hmap.continuousOn
      (fun p hp => hball p.1 hp.1 p.2 (sphere_subset_closedBall hp.2))
  have hkernel : ContinuousOn (fun p : (Fin n → ℂ) × ℂ => (p.2 ^ 2)⁻¹)
      (V ×ˢ sphere (0 : ℂ) R) := by
    apply (continuous_snd.pow 2).continuousOn.inv₀
    intro p hp
    apply pow_ne_zero
    intro hp0
    have hnorm : ‖p.2‖ = R := by
      simpa only [mem_sphere_iff_norm, sub_zero] using hp.2
    rw [hp0, norm_zero] at hnorm
    exact hR.ne' hnorm.symm
  have hint := continuousAt_circleIntegral
    (F := fun y z => (z ^ 2)⁻¹ * f (y + z • v)) (c := 0)
    hR.le hV hxV (hkernel.fun_mul hvalue)
  have hnormalized := hint.const_mul ((2 * π * I : ℂ)⁻¹)
  have heq : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * π * I : ℂ)⁻¹ * ∮ z in C(0, R), (z ^ 2)⁻¹ * f (y + z • v)) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact fderiv_apply_eq_circleIntegral hU hf y v hR (hball y hy)
  exact hnormalized.congr_of_eventuallyEq heq

/-- An operator on a finite coordinate space is the finite sum of its
coordinate projections, weighted by its values on coordinate basis vectors. -/
theorem clm_eq_sum_basis {n : ℕ} (L : (Fin n → ℂ) →L[ℂ] ℂ) :
    L = ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (L (Pi.single i 1)) := by
  ext z
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  have hz : (∑ i : Fin n, z i • (Pi.single i 1 : Fin n → ℂ)) = z := by
    ext j
    simp [Pi.single_apply]
  calc
    L z = L (∑ i : Fin n, z i • (Pi.single i 1 : Fin n → ℂ)) := congrArg L hz.symm
    _ = _ := by simp only [map_sum, map_smul]

/-- Complex differentiability on an open finite-dimensional domain forces
the full Fréchet derivative to be continuous. -/
theorem continuousAt_fderiv {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : Fin n → ℂ} (hx : x ∈ U) : ContinuousAt (fderiv ℂ f) x := by
  have heq : fderiv ℂ f = (fun y => ∑ i : Fin n,
      (ContinuousLinearMap.proj i).smulRight (fderiv ℂ f y (Pi.single i 1))) :=
    funext (fun y => clm_eq_sum_basis (fderiv ℂ f y))
  rw [heq]
  apply tendsto_finsetSum
  intro i _
  change ContinuousAt (fun y => ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) ℂ
    (ContinuousLinearMap.proj i) (fderiv ℂ f y (Pi.single i 1))) x
  exact (ContinuousLinearMap.smulRightL ℂ (Fin n → ℂ) ℂ
    (ContinuousLinearMap.proj i)).continuous.continuousAt.comp
      (continuousAt_fderiv_apply hU hf hx (Pi.single i 1))

/-- A complex differentiable scalar function on an open coordinate domain is
continuously differentiable there. -/
theorem contDiffOn_one_of_differentiableOn {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  change ContDiffOn ℂ ((0 : ℕ∞ω) + 1) f U
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hf, by simp, contDiffOn_zero.mpr
    (fun x hx => (continuousAt_fderiv hU hf hx).continuousWithinAt)⟩

/-- The same regularity holds for maps between finite complex coordinate
spaces, by applying the scalar result to each target coordinate. -/
theorem contDiffOn_one_of_differentiableOn_pi {n m : ℕ}
    {f : (Fin n → ℂ) → (Fin m → ℂ)} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U := by
  apply contDiffOn_pi.mpr
  intro i
  have heval : Differentiable ℂ (fun z : Fin m → ℂ => z i) := differentiable_apply i
  exact contDiffOn_one_of_differentiableOn hU (heval.comp_differentiableOn hf)

/-- Coordinate transport gives continuous differentiability for holomorphic
maps between arbitrary finite-dimensional complex normed spaces. -/
theorem contDiffOn_one_of_differentiableOn_finiteDimensional
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  let e := (Module.finBasis ℂ E).equivFunL
  let e' := (Module.finBasis ℂ F).equivFunL
  have hd : DifferentiableOn ℂ (e' ∘ f ∘ e.symm) (e.symm ⁻¹' U) :=
    e'.differentiable.comp_differentiableOn
      (hf.comp e.symm.differentiable.differentiableOn (mapsTo_preimage e.symm U))
  have hc := contDiffOn_one_of_differentiableOn_pi (hU.preimage e.symm.continuous) hd
  have hmaps : MapsTo e U (e.symm ⁻¹' U) := by
    intro x hx
    simpa only [mem_preimage, e.symm_apply_apply] using hx
  have hret := e'.symm.contDiff.comp_contDiffOn (hc.comp e.contDiff.contDiffOn hmaps)
  simpa only [Function.comp_def, e.symm_apply_apply, e'.symm_apply_apply] using hret

/-- A holomorphic coordinate map with an invertible derivative has an actual
local inverse which is holomorphic on its open domain. -/
theorem exists_holomorphic_localInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U)
    (e : E ≃L[ℂ] F)
    (he : fderiv ℂ f x = e.toContinuousLinearMap) :
    ∃ q : OpenPartialHomeomorph E F,
      x ∈ q.source ∧ (q : E → F) = f ∧
      DifferentiableOn ℂ q q.source ∧ DifferentiableOn ℂ q.symm q.target := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hcd : ContDiffAt ℂ 1 f x :=
    (contDiffOn_one_of_differentiableOn_finiteDimensional hU hf).contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  let q₀ := hcd.toOpenPartialHomeomorph f hd (by simp)
  have hx₀ : x ∈ q₀.source := hcd.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hinv : ContDiffAt ℂ 1 q₀.symm (q₀ x) := hcd.to_localInverse hd (by simp)
  refine ⟨q₀.restrContDiff ℂ 1 (by simp), ⟨hx₀, hcd, hinv⟩, rfl, ?_, ?_⟩
  · exact (q₀.contDiffOn_restrContDiff_source ℂ (by simp)).differentiableOn one_ne_zero
  · exact (q₀.contDiffOn_restrContDiff_target ℂ (by simp)).differentiableOn one_ne_zero

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicRegularity.Constructions.Regularity
