import OAI.RepresentationTheory.Theta.Geometric.Period.ThetaAt
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # Cover Sheets -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CoverSheets

noncomputable section

/-! A holomorphic covering with bijective differential has genuine smooth
local inverse sheets. The continuous inverse is supplied by the covering. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

section LocalInverse

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [TopologicalSpace N] [ChartedSpace W N]

/-- Invertibility of the complex derivative makes the actual continuous
local inverse complex differentiable. -/
theorem mdifferentiableAt_local_inverse
    (e : OpenPartialHomeomorph M N) {x : M} (hx : x ∈ e.source)
    (hf : MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, W) e x)
    (hbij : Function.Bijective (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) e x)) :
    MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, V) e.symm (e x) := by
  let a := chartAt V x x
  let u : OpenPartialHomeomorph V W :=
    (chartAt V x).symm.trans (e.trans (chartAt W (e x)))
  have ha : a ∈ u.source := by
    change a ∈ (chartAt V x).target ∧
      (chartAt V x).symm a ∈ e.source ∧
      e ((chartAt V x).symm a) ∈ (chartAt W (e x)).source
    simpa only [a, mem_chart_target, mem_chart_source, true_and, and_true,
      (chartAt V x).left_inv (mem_chart_source V x)] using hx
  have hua : u a = chartAt W (e x) (e x) := by
    change chartAt W (e x) (e ((chartAt V x).symm (chartAt V x x))) = _
    rw [(chartAt V x).left_inv (mem_chart_source V x)]
  have hd : DifferentiableAt ℂ u a := by
    simpa only [u, a, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.range_id, differentiableWithinAt_univ,
      OpenPartialHomeomorph.coe_trans, Function.comp_assoc]
      using hf.differentiableWithinAt_writtenInExtChartAt
  have hderiv : (show V →L[ℂ] W from mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) e x) =
      fderiv ℂ u a := by
    have he := hf.mfderiv
    simp only [TangentSpace, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.range_id, fderivWithin_univ] at he
    convert! he using 1
  let A : V ≃L[ℂ] W :=
    (LinearEquiv.ofBijective (fderiv ℂ u a).toLinearMap (hderiv ▸ hbij)).toContinuousLinearEquiv
  have hA : (A : V →L[ℂ] W) = fderiv ℂ u a := by ext z; rfl
  have hu : HasFDerivAt u (A : V →L[ℂ] W) (u.symm (u a)) := by
    rw [u.left_inv ha, hA]
    exact hd.hasFDerivAt
  have hi := (u.hasFDerivAt_symm (u.map_source ha) hu).differentiableAt
  rw [hua] at hi
  apply (mdifferentiableAt_iff e.symm (e x)).mpr
  refine ⟨e.symm.continuousAt (e.map_source hx), ?_⟩
  simpa only [u, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
    e.left_inv hx,
    writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, differentiableWithinAt_univ,
    Function.comp_assoc] using hi

end LocalInverse

open OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity

theorem holomorphicCover_isLocalDiffeomorph
    {V W M N : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℂ, V) ∞ M]
    [TopologicalSpace N] [ChartedSpace W N] [IsManifold 𝓘(ℂ, W) ∞ N]
    (f : M → N) (hcover : IsCoveringMap f)
    (hf : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) f)
    (hbij : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) f x)) :
    IsLocalDiffeomorph 𝓘(ℂ, V) 𝓘(ℂ, W) ∞ f := by
  intro x
  obtain ⟨e, hx, he⟩ := hcover.isLocalHomeomorph x
  have hinv : MDifferentiable 𝓘(ℂ, W) 𝓘(ℂ, V)
      (fun y : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens N) => e.symm y) := by
    intro y
    have hi := mdifferentiableAt_local_inverse e (e.map_target y.property)
      (he ▸ hf (e.symm y)) (he ▸ hbij (e.symm y))
    rw [e.right_inv y.property] at hi
    exact hi.comp y ((contMDiff_subtype_val (I := 𝓘(ℂ, W)) (n := ∞)).mdifferentiable (by simp) y)
  have hs := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hf
  have his := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hinv
  let p : PartialDiffeomorph 𝓘(ℂ, V) 𝓘(ℂ, W) M N ∞ :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn 𝓘(ℂ, V) 𝓘(ℂ, W) ∞ (e : M → N) e.source
        rw [← he]
        exact hs.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        exact (contMDiffAt_subtype_iff.mp (his ⟨y, hy⟩)).contMDiffWithinAt }
  exact ⟨p, hx, fun y _ => congrFun he y⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CoverSheets
