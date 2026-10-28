import OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection
import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import OAI.Analysis.DifferentialForms.Manifold.SquareZeroD

/-! # Polarization Curvature -/

namespace OAI.RepresentationTheory.Theta.Geometric.PolarizationCurvature

noncomputable section

/-! The actual exterior derivative of the metric connection has
positive (1,1) curvature normalized by the original integral form. -/

open OAI.Analysis.DifferentialForms.Manifold.Bidegree
open scoped ContDiff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

local instance : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V

def polarizationConnectionFormLinear : V →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue V 1 :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℂ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp (PolarizationConnection.polarizationConnection H)

@[simp] theorem polarizationConnectionFormLinear_apply (z : V) (v : Fin 1 → V) :
    polarizationConnectionFormLinear H z v = -(Real.pi : ℂ) * H z (v 0) := rfl

def polarizationConnectionForm : Analysis.DifferentialForms.Manifold.Basic.SmoothForm V 1 :=
  Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth (polarizationConnectionFormLinear H) (polarizationConnectionFormLinear H).contDiff

def polarizationCurvature : Analysis.DifferentialForms.Manifold.Basic.SmoothForm V 2 := Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (polarizationConnectionForm H)

theorem polarizationCurvature_apply (z : V) (v : Fin 2 → V) :
    polarizationCurvature H z v = -(Real.pi : ℂ) * (H (v 0) (v 1) - H (v 1) (v 0)) := by
  change extDeriv (polarizationConnectionFormLinear H : V → Analysis.DifferentialForms.Manifold.Basic.FormValue V 1) z v = _
  rw [extDeriv, (polarizationConnectionFormLinear H).fderiv,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    polarizationConnectionFormLinear_apply, Fin.removeNth, Fin.succAbove]
  norm_num
  ring

theorem polarizationCurvature_closed : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (polarizationCurvature H) = 0 :=
  Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_d (polarizationConnectionForm H)

theorem polarizationCurvature_translation (l z : V) :
    polarizationCurvature H (z + l) = polarizationCurvature H z := by
  ext v
  rw [polarizationCurvature_apply, polarizationCurvature_apply]

theorem polarizationCurvature_hasBidegree (z : V) : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 1 (polarizationCurvature H z) := by
  intro a v
  change polarizationCurvature H z (fun i : Fin 2 => (a : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 a * polarizationCurvature H z v
  rw [polarizationCurvature_apply, polarizationCurvature_apply]
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, starRingEnd_apply,
    smul_eq_mul, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one]
  ring

theorem polarizationCurvature_normalized (hsym : ∀ u v, H v u = star (H u v))
    (z : V) (v : Fin 2 → V) :
    (Complex.I / (2 * (Real.pi : ℂ))) * polarizationCurvature H z v =
      ((H (v 0) (v 1)).im : ℂ) := by
  rw [polarizationCurvature_apply, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew H hsym]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp]
  ring_nf
  simp [Complex.I_sq]

theorem polarizationCurvature_positive (hsym : ∀ u v, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (z u : V) (hu : u ≠ 0) :
    0 < ((Complex.I / (2 * (Real.pi : ℂ))) * polarizationCurvature H z ![u, Complex.I • u]).re := by
  rw [polarizationCurvature_normalized H hsym, Complex.ofReal_re]
  change 0 < (H u (Complex.I • u)).im
  rw [Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_imaginary_mul_I]
  exact hpos u hu

end

end OAI.RepresentationTheory.Theta.Geometric.PolarizationCurvature
