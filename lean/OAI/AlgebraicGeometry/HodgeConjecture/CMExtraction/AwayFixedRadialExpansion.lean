import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveRadialSpan
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorCoefficients

/-! # Away Fixed Radial Expansion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayFixedRadialExpansion.Local

noncomputable section

/-! Decompose an actual active-and-away fixed test into radial families
that all retain the same away level. Uniqueness of ball coefficients
prevents the auxiliary invariance from being lost in the expansion. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.TensorCoefficients

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem active_fixed_radial_coefficient_expansion (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (hf : f ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D)) :
    ∃ a : ℤ →₀ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ),
      RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ) (Radial.TensorCoefficients.radialTensorSum q a) = f := by
  let C := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ)
  have hm : ActiveRadialSpan.Local.auxiliaryRadialSpan q μ ≤ (LinearMap.range (Radial.TensorCoefficients.radialTensorSum q)).comap C.symm.toLinearMap := by
    rw [Radial.TensorCoefficients.radialTensorSum_range]
    apply Submodule.span_le.mpr
    rintro _ ⟨b, φ, rfl⟩
    change C.symm (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) ∈
      Submodule.span ℂ {F | ∃ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ)),
        F = RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ}
    rw [show AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b = C (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) φ) from
      RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.finiteRadialEmbedding_tensor q _ _ _ _ b, C.symm_apply_apply]
    exact Submodule.subset_span ⟨b, φ, rfl⟩
  obtain ⟨a, ha⟩ := hm (ActiveRadialSpan.Local.active_fixed_mem_auxiliaryRadialSpan q e μ D f hf)
  exact ⟨a, by rw [ha]; exact C.apply_symm_apply f⟩

theorem away_fixed_radial_coefficient_expansion
    (L : Subgroup MpF)
    (hL : ∀ m ∈ L, ∀ p s : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.finite.project m).val.mulVec (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ s)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ s))
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3))
    (hf : f ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D))
    (haway : f ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs L D.finite.action) :
    ∃ a : ℤ →₀ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ),
      RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ) (Radial.TensorCoefficients.radialTensorSum q a) = f ∧
      ∀ (k : ℤ) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q),
        AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ (a k) b ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs L D.finite.action := by
  obtain ⟨a, ha⟩ := active_fixed_radial_coefficient_expansion q e μ D f hf
  refine ⟨a, ha, ?_⟩
  intro k b m hm
  obtain ⟨V, hV⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteAuxiliaryAction.Realization.finiteWeil_auxiliary_action q μ D m (hL m hm)
  let C := RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ)
  have hOp : (D.finite.action m).toLinearMap.comp C.toLinearMap =
      C.toLinearMap.comp (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V).toLinearMap := by
    apply RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.test_linear_ext
    intro x y
    change D.finite.action m (C (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest x y)) = C (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest x y))
    rw [RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom_tensor]
    exact hV x y
  have hfix : RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V (Radial.TensorCoefficients.radialTensorSum q a) = Radial.TensorCoefficients.radialTensorSum q a := by
    apply C.injective
    have hh := LinearMap.congr_fun hOp (Radial.TensorCoefficients.radialTensorSum q a)
    change D.finite.action m (C (Radial.TensorCoefficients.radialTensorSum q a)) = C (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.rightTestHom V (Radial.TensorCoefficients.radialTensorSum q a)) at hh
    rw [ha, haway m hm] at hh
    exact hh.symm.trans ha.symm
  have hk := Radial.TensorCoefficients.radialTensorSum_fixed_coefficients q a V hfix k
  have he : AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ (a k) b = C (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorTest (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q b) (a k)) :=
    RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.finiteRadialEmbedding_tensor q _ _ _ _ b
  rw [he, hV, hk]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayFixedRadialExpansion.Local
