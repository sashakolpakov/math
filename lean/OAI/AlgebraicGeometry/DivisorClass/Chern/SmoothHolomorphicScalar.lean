import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ManifoldZeroForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConjugateProjection
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Smooth Holomorphic Scalar -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothHolomorphicScalar

noncomputable section

/-! Original holomorphic functions and their conjugates in the genuine scalar zero-form construction. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

def holomorphicFunctionAsSmoothOpen (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨g, Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex g.property⟩

def conjugateSmoothOpenFunction (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨fun x => conj (f x), Complex.conjCLE.contDiff.contMDiff.comp f.property⟩

theorem smoothScalarOpenZeroForm_holomorphic (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicFunctionAsSmoothOpen g) = Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm g := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply]
  rfl

theorem smoothScalarOpenZeroForm_conjugate (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    SmoothScalarForm.smoothScalarOpenZeroForm (conjugateSmoothOpenFunction f) = Open.ConjugateForms.openManifoldConjugate (SmoothScalarForm.smoothScalarOpenZeroForm f) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_apply, Open.ConjugateForms.openManifoldConjugate_apply, SmoothScalarForm.smoothScalarOpenZeroForm_apply]
  rfl

theorem smoothHolomorphicScalar_dbar_zero (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicFunctionAsSmoothOpen g)) = 0 := by
  rw [smoothScalarOpenZeroForm_holomorphic]
  exact Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_d g

theorem smoothHolomorphicScalar_holomorphicPart_d (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    Manifold.OneFormProjection.openManifoldOnePart (-Complex.I)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicFunctionAsSmoothOpen g))) =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicFunctionAsSmoothOpen g)) := by
  have h := Manifold.OneFormProjection.openManifoldOnePart_add
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicFunctionAsSmoothOpen g)))
  rw [Manifold.OneFormProjection.openManifoldOnePart_d, smoothHolomorphicScalar_dbar_zero, add_zero] at h
  exact h

theorem smoothConjugateHolomorphicScalar_holomorphicPart_d (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
      (SmoothScalarForm.smoothScalarOpenZeroForm (conjugateSmoothOpenFunction (holomorphicFunctionAsSmoothOpen g)))) = 0 := by
  rw [smoothScalarOpenZeroForm_conjugate, Open.ConjugateForms.openManifoldConjugate_d]
  have h := Open.ConjugateProjection.openManifoldConjugate_onePart Complex.I
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (holomorphicFunctionAsSmoothOpen g)))
  rw [Complex.conj_I, Manifold.OneFormProjection.openManifoldOnePart_d, smoothHolomorphicScalar_dbar_zero, Open.ConjugateProjection.openManifoldConjugate_zero] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothHolomorphicScalar
