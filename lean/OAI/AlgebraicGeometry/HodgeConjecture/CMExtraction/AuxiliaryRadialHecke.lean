import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalHecke

/-! # Auxiliary Radial Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialHecke.Local

noncomputable section

/-! The actual local finite Hecke action on radial tensors with arbitrary
auxiliary test functions. The auxiliary vacuum is one specialization. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]

def auxiliaryFiniteRadialEmbedding (μ : Place) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) :=
  RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding.Realization.finiteRadialEmbedding q (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ) φ.val φ.property.1 φ.property.2

variable {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)
  (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ))

theorem activeFiniteLift_auxiliary_radial (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
    (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D g) (auxiliaryFiniteRadialEmbedding q μ φ b)).val x =
      b.val ((g⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) * φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2 := by
  rw [ActiveLocalLift.activeFiniteLift_block_substitution]
  change b.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).1) *
    φ.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).2) = _
  rw [Homeomorph.apply_symm_apply]

theorem auxiliaryRadial_active_fixed (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    auxiliaryFiniteRadialEmbedding q μ φ b ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D) := by
  intro g hg
  apply Subtype.ext
  funext x
  rw [show ActiveLocalHecke.activeFiniteRepresentation q e μ D g = D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D g) from rfl,
    activeFiniteLift_auxiliary_radial]
  have h := congrFun (Radial.Hecke.radial_integral_fixed q b g hg) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x)
  change b.val ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) :
    Matrix (Fin 3) (Fin 3) ℚ_[q]) *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) = _ at h
  rw [← map_inv] at h
  exact congrArg (fun a : ℂ => a * φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2) h

def auxiliaryRadialFixedEmbedding : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D) :=
  (auxiliaryFiniteRadialEmbedding q μ φ).codRestrict _ (auxiliaryRadial_active_fixed q e μ D φ)

theorem auxiliaryRadial_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D) T
      (auxiliaryFiniteRadialEmbedding q μ φ b) =
        auxiliaryFiniteRadialEmbedding q μ φ (Radial.Action.sphericalRadialAction q T b) := by
  apply Subtype.ext
  funext x
  have hexp := ActiveLocalHecke.weilOperator_evaluation (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D) T
    (auxiliaryFiniteRadialEmbedding q μ φ b)
    ((LinearMap.proj x).comp (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)).subtype)
  change ((LinearMap.proj x).comp (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)).subtype)
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (ActiveLocalHecke.activeFiniteRepresentation q e μ D) T
      (auxiliaryFiniteRadialEmbedding q μ φ b)) = _
  rw [hexp]
  change (∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
        (D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D c.out) (auxiliaryFiniteRadialEmbedding q μ φ b)).val x) =
    (Radial.Hecke.sphericalFunctionAction q T b.val) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) *
      φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  simp_rw [activeFiniteLift_auxiliary_radial]
  have hfun : (Radial.Hecke.sphericalFunctionAction q T b.val) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) =
      ∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
        ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
          (Radial.Hecke.matrixSubstitution q c.out b.val) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) :=
    ActiveLocalHecke.weilOperator_evaluation (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Radial.Hecke.matrixSubstitution q) T b.val
      (LinearMap.proj (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x))
  rw [hfun]
  change (∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
        (b.val ((c.out⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) *
          φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2)) =
    (∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
        b.val ((↑((Matrix.SpecialLinearGroup.toGL c.out)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]) *ᵥ
          RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x)) * φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  simp only [← map_inv, Finset.sum_mul, mul_assoc]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialHecke.Local
