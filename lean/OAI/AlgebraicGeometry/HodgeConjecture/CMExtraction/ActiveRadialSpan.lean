import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialHecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorSpan

/-! # Active Radial Span -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveRadialSpan.Local

noncomputable section

/-! Every finite test function fixed by the actual integral active group
is spanned by radial tensors with arbitrary auxiliary tests. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorSpan

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

def auxiliaryRadialSpan : Submodule ℂ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :=
  Submodule.span ℂ {f | ∃ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ)),
    f = AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b}

theorem active_fixed_mem_auxiliaryRadialSpan (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (hf : f ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D)) :
    f ∈ auxiliaryRadialSpan q μ := by
  let C := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ)
  let F := C.symm f
  have hF := Radial.TensorSpan.integral_fixed_tensor_mem_span q F (by
    intro g hg x y
    have h := congrArg (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) =>
      z.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm (x, y))) (hf g hg)
    change (D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D g) f).val
      ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm (x, y)) = _ at h
    rw [ActiveLocalLift.activeFiniteLift_block_substitution] at h
    change f.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm
      ((g⁻¹).val.mulVec (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm (x, y))).1,
        (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm (x, y))).2)) = _ at h
    rw [Homeomorph.apply_symm_apply] at h
    exact h)
  have hmap : Submodule.span ℂ {F | ∃ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
      (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ)), F = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ} ≤
      (auxiliaryRadialSpan q μ).comap C.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, φ, rfl⟩
    exact Submodule.subset_span ⟨b, φ,
      (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.finiteRadialEmbedding_tensor q (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ) φ.val φ.property.1 φ.property.2 b).symm⟩
  have h := hmap hF
  change C (C.symm f) ∈ auxiliaryRadialSpan q μ at h
  rwa [C.apply_symm_apply] at h

theorem active_fixed_space_eq_auxiliaryRadialSpan :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D) =
      auxiliaryRadialSpan q μ := by
  apply le_antisymm
  · exact active_fixed_mem_auxiliaryRadialSpan q e μ D
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, φ, rfl⟩
    exact AuxiliaryRadialHecke.Local.auxiliaryRadial_active_fixed q e μ D φ b

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveRadialSpan.Local
