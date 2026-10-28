import OAI.AlgebraicGeometry.Cycles.Functoriality.EtaleDifferential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Analytic Inverse -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticInverse.Construction

noncomputable section

open scoped ContDiff _root_.Manifold _root_.Topology
open Filter IsManifold

/-- The analytic inverse function theorem, restricted so that both
directions are analytic throughout their open domains. -/
theorem exists_analytic_localInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x)
    (hbij : Function.Bijective (fderiv ℂ f x)) :
    ∃ q : OpenPartialHomeomorph E F,
      x ∈ q.source ∧ (q : E → F) = f ∧
      ContDiffOn ℂ ω q q.source ∧ ContDiffOn ℂ ω q.symm q.target := by
  let := FiniteDimensional.complete ℂ E
  let L : E ≃L[ℂ] F :=
    (LinearEquiv.ofBijective (fderiv ℂ f x).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt f L.toContinuousLinearMap x := by
    change HasFDerivAt f (fderiv ℂ f x) x
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let q₀ := hf.toOpenPartialHomeomorph f hd (by simp)
  have hx : x ∈ q₀.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : ContDiffAt ℂ ω q₀.symm (q₀ x) := hf.to_localInverse hd (by simp)
  refine ⟨q₀.restrContDiff ℂ ω (by simp), ⟨hx, hf, hi⟩, rfl, ?_, ?_⟩
  · exact q₀.contDiffOn_restrContDiff_source ℂ (by simp)
  · exact q₀.contDiffOn_restrContDiff_target ℂ (by simp)

/-- On equal-dimensional regular affine charts, an unramified map has
an actual analytic local inverse. -/
theorem exists_unramified_affineChart_localInverse
    {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    {n : ℕ} (h : A →ₐ[ℂ] B) (hh : h.toRingHom.FormallyUnramified)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
    (hfx : x.comp h ∈ f.source) :
    ∃ q : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ),
      e x ∈ q.source ∧ (q : (Fin n → ℂ) → (Fin n → ℂ)) =
        (fun z => f ((e.symm z).comp h)) ∧
      ContDiffOn ℂ ω q q.source ∧ ContDiffOn ℂ ω q.symm q.target := by
  have hinj := EtaleDifferential.Construction.fderiv_affineChartComap_injective_of_unramified h hh e f he hf x hx hfx
  exact exists_analytic_localInverse _ _
    (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx)
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩

/-- Invertibility in genuine manifold charts gives a local analytic
diffeomorphism on the original spaces. -/
theorem isLocalDiffeomorphAt_of_chart_bijective
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℂ, E)) ω M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℂ, F)) ω N]
    (g : M → N) (hg : Continuous g) (x : M)
    (e : OpenPartialHomeomorph M E) (f : OpenPartialHomeomorph N F)
    (he : e ∈ maximalAtlas (𝓘(ℂ, E)) ω M)
    (hf : f ∈ maximalAtlas (𝓘(ℂ, F)) ω N)
    (hx : x ∈ e.source) (hgx : g x ∈ f.source)
    (hC : ContDiffAt ℂ ω (fun z => f (g (e.symm z))) (e x))
    (hbij : Function.Bijective (fderiv ℂ (fun z => f (g (e.symm z))) (e x))) :
    IsLocalDiffeomorphAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) ω g x := by
  obtain ⟨q, hxq, hq, hqd, hqi⟩ := exists_analytic_localInverse _ _ hC hbij
  let e' : PartialDiffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, E)) M E ω :=
    { __ := e
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  let f' : PartialDiffeomorph (𝓘(ℂ, F)) (𝓘(ℂ, F)) N F ω :=
    { __ := f
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hf
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hf }
  let q' : PartialDiffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, F)) E F ω :=
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

/-- The complex inverse function theorem on the established manifold
structures, with the actual manifold differential as its hypothesis. -/
theorem isLocalDiffeomorphAt_of_bijective_mfderiv
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℂ, E)) ω M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℂ, F)) ω N]
    (g : M → N) (hg : ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, F)) ω g) (x : M)
    (hbij : Function.Bijective (mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) g x)) :
    IsLocalDiffeomorphAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) ω g x := by
  have hC := (contMDiffAt_iff_of_mem_source
    (mem_chart_source E x) (mem_chart_source F (g x))).mp (hg x)
  have hC' : ContDiffAt ℂ ω
      (fun z => chartAt F (g x) (g ((chartAt E x).symm z))) (chartAt E x x) := by
    simpa only [extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, contDiffWithinAt_univ] using hC.2
  have hder : mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) g x =
      fderiv ℂ (fun z => chartAt F (g x) (g ((chartAt E x).symm z)))
        (chartAt E x x) := by
    rw [((hg.of_le (show (1 : ℕ∞ω) ≤ ω from le_top)).mdifferentiableAt
      (x := x) one_ne_zero).mfderiv]
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]
    rfl
  exact isLocalDiffeomorphAt_of_chart_bijective g hg.continuous x
    (chartAt E x) (chartAt F (g x)) (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas (g x)) (mem_chart_source E x)
    (mem_chart_source F (g x)) hC' (hder ▸ hbij)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticInverse.Construction
