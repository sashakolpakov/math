import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParametricPullback

/-! # Cover Chart Sections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverChartSections.CM

noncomputable section

section

/-! ThetaCycle: fixed smooth local covering sections, with their actual source
atlas chart and coordinate domains made explicit. -/

open Set
open scoped _root_.Manifold ContDiff

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

structure CoverChartSection (f : M → N) (c : OpenPartialHomeomorph N F) where
  sourceChart : SmoothTopology.CM.SmoothAtlasChart E M
  sectionMap : N → M
  domain : Set N
  open_domain : IsOpen domain
  smooth : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ sectionMap domain
  right_inverse : ∀ y ∈ domain, f (sectionMap y) = y
  coordinateDomain : Set F
  open_coordinateDomain : IsOpen coordinateDomain
  chart_target : coordinateDomain ⊆ c.target
  section_domain : ∀ y ∈ coordinateDomain, c.symm y ∈ domain
  source_chart_domain : ∀ y ∈ coordinateDomain, sectionMap (c.symm y) ∈ sourceChart.val.source
  coordinate_smooth : ∀ y ∈ coordinateDomain,
    ContDiffAt ℝ ∞ (sourceChart.val ∘ sectionMap ∘ c.symm) y

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

theorem exists_cover_chart_section (f : M → N) (hsurj : Function.Surjective f)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (c : OpenPartialHomeomorph N F) (hc : c ∈ atlas F N) (x : F) (hx : x ∈ c.target) :
    ∃ D : CoverChartSection (E := E) f c, x ∈ D.coordinateDomain := by
  obtain ⟨z, hzy⟩ := hsurj (c.symm x)
  obtain ⟨φ, hz, he⟩ := hf z
  have hyφ : c.symm x ∈ φ.target := by
    rw [← hzy, he hz]
    exact φ.map_source hz
  have hsz : φ.symm (c.symm x) = z := by
    rw [← hzy, he hz]
    exact φ.left_inv hz
  let d : SmoothTopology.CM.SmoothAtlasChart E M := ⟨chartAt E z, chart_mem_atlas E z⟩
  let U : Set N := φ.target ∩ φ.symm ⁻¹' d.val.source
  have hU : IsOpen U :=
    φ.toOpenPartialHomeomorph.symm.isOpen_inter_preimage d.val.open_source
  have hxU : c.symm x ∈ U := by
    refine ⟨hyφ, ?_⟩
    change φ.symm (c.symm x) ∈ d.val.source
    rw [hsz]
    exact mem_chart_source E z
  let V : Set F := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.symm.isOpen_inter_preimage hU
  refine ⟨{
    sourceChart := d
    sectionMap := φ.symm
    domain := U
    open_domain := hU
    smooth := φ.contMDiffOn_invFun.mono (fun _ hy => hy.1)
    right_inverse := ?_
    coordinateDomain := V
    open_coordinateDomain := hV
    chart_target := fun _ hy => hy.1
    section_domain := fun _ hy => hy.2
    source_chart_domain := fun _ hy => hy.2.2
    coordinate_smooth := ?_ }, ⟨hx, hxU⟩⟩
  · intro y hy
    exact (he (φ.map_target hy.1)).trans (φ.right_inv hy.1)
  · intro y hy
    exact Analysis.DifferentialForms.Manifold.ManifoldPullback.contDiffAt_manifoldMap_inChart φ.symm c d.val hc d.property hy.1 hy.2.2
      ((φ.contMDiffOn_invFun (c.symm y) hy.2.1).contMDiffAt (φ.open_target.mem_nhds hy.2.1))

end

/-! ThetaCycle: full smooth convergence of actual descended forms follows
from local smooth parameter formulas for their covering pullbacks. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

theorem parametric_cover_forms_converge
    {P E F M N A : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactSpace F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : M → N) (hsurj : Function.Surjective f)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    {l : Filter A} (p : A → P) (p₀ : P) (hp : Tendsto p l (𝓝 p₀))
    (n : ℕ) (forms : A → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n)
    (hlocal : ∀ e : SmoothTopology.CM.SmoothAtlasChart E M, ∀ x ∈ e.val.target,
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∃ g : P → E → E [⋀^Fin n]→L[ℝ] ℂ,
          (∀ y ∈ U, ContDiffAt ℝ ∞ (Function.uncurry g) (p₀, y)) ∧
          (∀ᶠ a in l, ∀ y ∈ U, ((forms a).val.pullback (E := E) f).inChart e.val y = g (p a) y) ∧
          (∀ y ∈ U, (form.val.pullback (E := E) f).inChart e.val y = g p₀ y)) :
    let _ := SmoothTopology.CM.smoothFormTopology F N n
    Tendsto forms l (𝓝 form) := by
  apply LocalParametricForms.CM.local_parametric_forms_converge p p₀ hp n forms form
  intro c x hx
  obtain ⟨D, hxD⟩ := exists_cover_chart_section f hsurj hf c.val c.property x hx
  let h : F → E := D.sourceChart.val ∘ D.sectionMap ∘ c.val.symm
  have hxsource : h x ∈ D.sourceChart.val.target :=
    D.sourceChart.val.map_source (D.source_chart_domain x hxD)
  obtain ⟨U, hU, hxU, g, hg, hfg, h₀⟩ := hlocal D.sourceChart (h x) hxsource
  have hh : ContinuousOn h D.coordinateDomain :=
    fun y hy => (D.coordinate_smooth y hy).continuousAt.continuousWithinAt
  let W : Set F := D.coordinateDomain ∩ h ⁻¹' U
  have hW : IsOpen W := hh.isOpen_inter_preimage D.open_coordinateDomain hU
  let G : P → F → F [⋀^Fin n]→L[ℝ] ℂ :=
    fun q y => (g q (h y)).compContinuousLinearMap (fderiv ℝ h y)
  refine ⟨W, hW, ⟨hxD, hxU⟩, G, ?_, ?_, ?_⟩
  · intro y hy
    exact ParametricPullback.CM.parametric_covector_pullback_smoothAt n g h p₀ y (hg (h y) hy.2)
      (D.coordinate_smooth y hy.1)
  · filter_upwards [hfg] with a ha
    intro y hy
    have hc := DescentChartFormula.CM.descended_form_chart_formula f hf.contMDiff D.sectionMap D.domain D.open_domain
      D.smooth D.right_inverse n ((forms a).val.pullback (E := E) f) (forms a).val rfl
      c.val D.sourceChart.val c.property D.sourceChart.property y (D.chart_target hy.1)
      (D.section_domain y hy.1) (D.source_chart_domain y hy.1)
    rw [hc]
    change (((forms a).val.pullback (E := E) f).inChart D.sourceChart.val (h y)).compContinuousLinearMap
      (fderiv ℝ h y) = G (p a) y
    rw [ha (h y) hy.2]
  · intro y hy
    have hc := DescentChartFormula.CM.descended_form_chart_formula f hf.contMDiff D.sectionMap D.domain D.open_domain
      D.smooth D.right_inverse n (form.val.pullback (E := E) f) form.val rfl
      c.val D.sourceChart.val c.property D.sourceChart.property y (D.chart_target hy.1)
      (D.section_domain y hy.1) (D.source_chart_domain y hy.1)
    rw [hc]
    change ((form.val.pullback (E := E) f).inChart D.sourceChart.val (h y)).compContinuousLinearMap
      (fderiv ℝ h y) = G p₀ y
    rw [h₀ (h y) hy.2]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverChartSections.CM
