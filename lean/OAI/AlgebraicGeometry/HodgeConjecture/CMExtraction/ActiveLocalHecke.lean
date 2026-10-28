import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action

/-! # Active Local Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalHecke

noncomputable section

/-! The exact finite-cover SL3 action fixes radial inputs at integral level
and realizes the same finite spherical coset sum as the radial model. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action
open scoped Classical _root_.Matrix

theorem weilOperator_evaluation {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (K : Subgroup G) (ρ : G →* (V ≃ₗ[ℂ] V)) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra K)
    (v : V) (l : V →ₗ[ℂ] ℂ) :
    l (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator K ρ T v) =
      ∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T).support, ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel K T c : ℚ) : ℂ) * l (ρ c.out v) := by
  simp only [RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator, Finsupp.sum, LinearMap.sum_apply,
    map_sum, LinearMap.smul_apply, map_smul, smul_eq_mul, LinearEquiv.coe_coe]

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

def activeFiniteRepresentation : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :=
  D.finite.action.comp (ActiveLocalLift.activeFiniteLift q e μ D)

theorem canonicalRadial_active_fixed (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (activeFiniteRepresentation q e μ D) := by
  intro g hg
  apply Subtype.ext
  funext x
  rw [show activeFiniteRepresentation q e μ D g = D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D g) from rfl,
    ActiveLocalLift.activeFiniteLift_radial]
  have h := congrFun (Radial.Hecke.radial_integral_fixed q b g hg) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x)
  change b.val ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) :
    Matrix (Fin 3) (Fin 3) ℚ_[q]) *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) = _ at h
  rw [← map_inv] at h
  exact congrArg (fun a : ℂ => a * (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.finiteAwayVacuum q μ).val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2) h

def activeRadialEmbedding : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (activeFiniteRepresentation q e μ D) :=
  (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ).codRestrict _ (canonicalRadial_active_fixed q e μ D)

theorem activeRadialEmbedding_injective : Function.Injective (activeRadialEmbedding q e μ D) := by
  intro b c h
  exact RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding_injective q μ (congrArg Subtype.val h)

theorem activeRadial_hecke (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (activeFiniteRepresentation q e μ D) T
      (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) =
        RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ (Radial.Action.sphericalRadialAction q T b) := by
  apply Subtype.ext
  funext x
  have hexp := weilOperator_evaluation (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (activeFiniteRepresentation q e μ D) T
    (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)
    ((LinearMap.proj x).comp (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)).subtype)
  change ((LinearMap.proj x).comp (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)).subtype)
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (activeFiniteRepresentation q e μ D) T
      (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)) = _
  rw [hexp]
  change (∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
        (D.finite.action (ActiveLocalLift.activeFiniteLift q e μ D c.out) (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)).val x) =
    (Radial.Hecke.sphericalFunctionAction q T b.val) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) *
      (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.finiteAwayVacuum q μ).val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  simp_rw [ActiveLocalLift.activeFiniteLift_radial]
  have hfun : (Radial.Hecke.sphericalFunctionAction q T b.val) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) =
      ∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
        ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
          (Radial.Hecke.matrixSubstitution q c.out b.val) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) :=
    weilOperator_evaluation (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Radial.Hecke.matrixSubstitution q) T b.val
      (LinearMap.proj (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x))
  rw [hfun]
  change (∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
        (b.val ((c.out⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) *
          (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.finiteAwayVacuum q μ).val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2)) =
    (∑ c ∈ (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).support,
      ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T c : ℚ) : ℂ) *
        b.val ((↑((Matrix.SpecialLinearGroup.toGL c.out)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]) *ᵥ
          RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x)) * (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.finiteAwayVacuum q μ).val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  simp only [← map_inv, Finset.sum_mul, mul_assoc]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalHecke
