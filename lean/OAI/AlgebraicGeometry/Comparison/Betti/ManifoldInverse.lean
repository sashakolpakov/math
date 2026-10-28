import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Manifold Inverse -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldInverse.Smooth

noncomputable section

/-!
# Smooth local inverses for the open-subscheme comparison

The real inverse function theorem is applied in actual manifold charts.
The chart argument follows the generic construction in AnalyticInverse,
using real analyticity and only the native manifold and calculus libraries.
-/

open Filter IsManifold
open scoped _root_.Manifold ContDiff _root_.Topology

theorem exists_realAnalytic_localInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F) (x : E) (hf : ContDiffAt ℝ ω f x)
    (hbij : Function.Bijective (fderiv ℝ f x)) :
    ∃ q : OpenPartialHomeomorph E F,
      x ∈ q.source ∧ (q : E → F) = f ∧
      ContDiffOn ℝ ω q q.source ∧ ContDiffOn ℝ ω q.symm q.target := by
  let := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt f L.toContinuousLinearMap x := by
    change HasFDerivAt f (fderiv ℝ f x) x
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let q₀ := hf.toOpenPartialHomeomorph f hd (by simp)
  have hx : x ∈ q₀.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : ContDiffAt ℝ ω q₀.symm (q₀ x) := hf.to_localInverse hd (by simp)
  refine ⟨q₀.restrContDiff ℝ ω (by simp), ⟨hx, hf, hi⟩, rfl, ?_, ?_⟩
  · exact q₀.contDiffOn_restrContDiff_source ℝ (by simp)
  · exact q₀.contDiffOn_restrContDiff_target ℝ (by simp)

theorem isLocalDiffeomorphAt_of_realAnalytic_chart_bijective
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ω M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ω N]
    (g : M → N) (hg : Continuous g) (x : M)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ω M) (hf : f ∈ maximalAtlas 𝓘(ℝ, F) ω N)
    (hx : x ∈ e.source) (hgx : g x ∈ f.source)
    (hC : ContDiffAt ℝ ω (fun z => f (g (e.symm z))) (e x))
    (hbij : Function.Bijective (fderiv ℝ (fun z => f (g (e.symm z))) (e x))) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ω g x := by
  obtain ⟨q, hxq, hq, hqd, hqi⟩ := exists_realAnalytic_localInverse _ _ hC hbij
  let e' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ω :=
    { __ := e
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  let f' : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) N F ω :=
    { __ := f
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hf
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hf }
  let q' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ω :=
    { __ := q
      contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.mpr hqd
      contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.mpr hqi }
  let l := (e'.trans q').trans f'.symm
  let r := l.toOpenPartialHomeomorph.restr (g ⁻¹' f.source)
  refine ⟨{ __ := r
            contMDiffOn_toFun := l.contMDiffOn_toFun.mono Set.inter_subset_left
            contMDiffOn_invFun := l.contMDiffOn_invFun.mono Set.inter_subset_left }, ?_, ?_⟩
  · change x ∈ l.toOpenPartialHomeomorph.source ∩ interior (g ⁻¹' f.source)
    refine ⟨?_, (f.open_source.preimage hg).interior_eq.symm ▸ hgx⟩
    change (x ∈ e.source ∧ e x ∈ q.source) ∧ q (e x) ∈ f.target
    refine ⟨⟨hx, hxq⟩, ?_⟩
    rw [hq]
    dsimp only
    rw [e.left_inv hx]
    exact f.map_source hgx
  · intro y hy
    change g y = f.symm (q (e y))
    change ((y ∈ e.source ∧ e y ∈ q.source) ∧ q (e y) ∈ f.target) ∧
      y ∈ interior (g ⁻¹' f.source) at hy
    rw [hq]
    dsimp only
    rw [e.left_inv hy.1.1.1]
    have hgy : y ∈ g ⁻¹' f.source := interior_subset hy.2
    exact (f.left_inv hgy).symm

theorem isLocalDiffeomorphAt_of_realAnalytic_bijective_mfderiv
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ω M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ω N]
    (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω g) (x : M)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ω g x := by
  have hC := (contMDiffAt_iff_of_mem_source
    (mem_chart_source E x) (mem_chart_source F (g x))).mp (hg x)
  have hC' : ContDiffAt ℝ ω
      (fun z => chartAt F (g x) (g ((chartAt E x).symm z))) (chartAt E x x) := by
    simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
      contDiffWithinAt_univ] using hC.2
  have hder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x =
      fderiv ℝ (fun z => chartAt F (g x) (g ((chartAt E x).symm z))) (chartAt E x x) := by
    rw [(hg.mdifferentiableAt (x := x) (by simp)).mfderiv]
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]
    rfl
  exact isLocalDiffeomorphAt_of_realAnalytic_chart_bijective g hg.continuous x
    (chartAt E x) (chartAt F (g x)) (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas (g x)) (mem_chart_source E x)
    (mem_chart_source F (g x)) hC' (hder ▸ hbij)

/-- A continuous local lift is smooth when its composite through a local diffeomorphism is smooth. -/
theorem contMDiff_lift_of_localDiffeomorph
    {E F G M N P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
    (f : M → N) (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ω f)
    (g : P → M) (hg : Continuous g) (hfg : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ (f ∘ g)) :
    ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ g := by
  intro x
  have hlocal := hf (g x)
  have hs := (hlocal.localInverse_contMDiffAt.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)).comp x (hfg x)
  have heq := hlocal.localInverse_eventuallyEq_left.comp_tendsto (hg.continuousAt :
    Tendsto g (𝓝 x) (𝓝 (g x)))
  exact hs.congr_of_eventuallyEq heq.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldInverse.Smooth
