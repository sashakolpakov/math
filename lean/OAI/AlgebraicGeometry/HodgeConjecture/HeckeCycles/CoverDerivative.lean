import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # Cover Derivative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverDerivative.CM

noncomputable section

/-! Local inverse differentiation for the actual holomorphic covers.
The continuous inverse already exists by the covering property, so the
ordinary inverse-derivative lemma applies without an extra regularity
hypothesis on the family. -/

open scoped Classical _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

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

variable {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace V M]
  [TopologicalSpace N] [ChartedSpace W N]
  [TopologicalSpace P] [ChartedSpace Z P]

/-- The map forced by the orbit relation is holomorphic, because on a
covering neighborhood it is the target cover composed with the actual
holomorphic local inverse of the source cover. -/
theorem factor_mdifferentiable
    (π : M → N) (ρ : M → P) (hπ : Function.Surjective π)
    (hcover : IsCoveringMap π)
    (hπdiff : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) π)
    (hbij : ∀ z, Function.Bijective (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) π z))
    (hρdiff : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, Z) ρ)
    (hfibers : ∀ z w, π z = π w → ρ z = ρ w) :
    MDifferentiable 𝓘(ℂ, W) 𝓘(ℂ, Z) (CoverFactor.CM.factor π ρ hπ) := by
  intro x
  obtain ⟨z, rfl⟩ := hπ x
  obtain ⟨e, hz, he⟩ := hcover.isLocalHomeomorph z
  have hd : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, V) e.symm (π z) := by
    rw [he]
    apply mdifferentiableAt_local_inverse e hz
    · rw [← he]; exact hπdiff z
    · rw [← he]; exact hbij z
  have hc : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, Z) (ρ ∘ e.symm) (π z) :=
    (hρdiff (e.symm (π z))).comp (π z) hd
  have htarget : π z ∈ e.target := he ▸ e.map_source hz
  have hsection : ∀ y ∈ e.target, π (e.symm y) = y := by
    intro y hy
    rw [he]
    exact e.right_inv hy
  have heq := CoverFactor.CM.factor_on_section π ρ hπ hfibers e.symm e.target hsection
  have hev : CoverFactor.CM.factor π ρ hπ =ᶠ[nhds (π z)] ρ ∘ e.symm :=
    Filter.eventuallyEq_of_mem (e.open_target.mem_nhds htarget) heq
  exact hev.mdifferentiableAt_iff.mpr hc

/-- Holomorphicity holds for any map with the forced commuting equation;
its equality with the constructed factor follows from surjectivity. -/
theorem descended_map_mdifferentiable
    (π : M → N) (ρ : M → P) (hπ : Function.Surjective π)
    (hcover : IsCoveringMap π)
    (hπdiff : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) π)
    (hbij : ∀ z, Function.Bijective (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) π z))
    (hρdiff : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, Z) ρ)
    (f : N → P) (hcomp : ∀ z, f (π z) = ρ z) :
    MDifferentiable 𝓘(ℂ, W) 𝓘(ℂ, Z) f := by
  have hfibers : ∀ z w, π z = π w → ρ z = ρ w := by
    intro z w hzw
    rw [← hcomp z, ← hcomp w, hzw]
  rw [CoverFactor.CM.factor_unique π ρ hπ f hcomp]
  exact factor_mdifferentiable π ρ hπ hcover hπdiff hbij hρdiff hfibers

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverDerivative.CM
