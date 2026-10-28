import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldZeroForms

/-! # Dolbeault Zero Kernel -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel

noncomputable section

/-! The genuine degree-zero manifold Dolbeault kernel consists of original holomorphic sections. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

def openManifoldZeroScalar (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) : M → ℂ :=
  fun x => a.extension x 0

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldZeroScalar_apply (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) (x : U) :
    openManifoldZeroScalar a x = a x 0 := by
  change a.extension x 0 = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldZeroScalar_reconstruct_chart (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (e : OpenPartialHomeomorph M E) :
    (fun y => constOfIsEmpty ℝ E (Fin 0) (openManifoldZeroScalar a (e.symm y))) =
      a.extension.inChart e := by
  funext y
  ext v
  change a.extension (e.symm y) 0 = a.extension (e.symm y) _
  congr 1
  exact Subsingleton.elim _ _

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldZeroScalar_chart_smooth (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) :
    ContDiffOn ℝ ∞ (openManifoldZeroScalar a ∘ e.symm) (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set E) := by
  have hs := (constOfIsEmptyLIE ℝ E ℂ (Fin 0)).symm.contDiff.comp_contDiffOn (a.smooth e he)
  apply hs.congr
  intro y _
  change a.extension (e.symm y) 0 = a.extension.inChart e y 0
  exact (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero_apply a.extension e y).symm

variable [FiniteDimensional ℂ E]

theorem openManifoldZeroScalar_holomorphic (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (ha : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a = 0) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ) ∞ (openManifoldZeroScalar a) (U : Set M) := by
  apply (Holomorphic.ManifoldCoordinates.contMDiffOn_complex_iff_chartCoordinates U _).mpr
  intro e he
  apply (DolbeaultOpen.contDiffOn_complex_iff_dolbeault_zero (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen
    (openManifoldZeroScalar_chart_smooth a e he)).mpr
  intro y hy
  change Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
    (fun z => constOfIsEmpty ℝ E (Fin 0) (openManifoldZeroScalar a (e.symm z))) y = 0
  rw [openManifoldZeroScalar_reconstruct_chart]
  have hz := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 => b.extension.inChart e y) ha
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local rfl (fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _) e he hy] at hz
  have hzero : (0 : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1).extension = 0 := Analysis.DifferentialForms.Manifold.Open.openManifoldFormExtension_zero U
  simpa only [hzero, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero, Pi.zero_apply] using hz

def holomorphicManifoldFunctionOfDbarZero (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (ha : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a = 0) : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) :=
  ⟨fun x => a x 0, by
    intro x
    have hc := (openManifoldZeroScalar_holomorphic a ha).contMDiffAt (U.isOpen.mem_nhds x.property)
    have ht := (contMDiffAt_subtype_iff (U := U) (x := x)).mpr hc
    simpa only [openManifoldZeroScalar_apply] using ht⟩

theorem holomorphicManifoldZeroForm_ofDbarZero (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (ha : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a = 0) :
    Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (holomorphicManifoldFunctionOfDbarZero a ha) = a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply]
  change a x 0 = a x v
  congr 1
  exact Subsingleton.elim _ _

theorem holomorphicManifoldZeroFormLinear_range (U : Opens M) :
    LinearMap.range (Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroFormLinear (E := E) U) =
      LinearMap.ker (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0) := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_d g
  · intro ha
    exact ⟨holomorphicManifoldFunctionOfDbarZero a ha, holomorphicManifoldZeroForm_ofDbarZero a ha⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel
