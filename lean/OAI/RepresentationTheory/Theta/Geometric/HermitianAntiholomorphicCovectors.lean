import OAI.RepresentationTheory.Theta.Geometric.HermitianAntiDual
import OAI.Analysis.DifferentialForms.Manifold.Bidegree

/-! # Hermitian Antiholomorphic Covectors -/

namespace OAI.RepresentationTheory.Theta.Geometric.HermitianAntiholomorphicCovectors

noncomputable section

/-! Every actual covector of type (0,1) is the Hermitian pairing with
a translation vector, with the original polarization's factor of pi. -/

set_option backward.isDefEq.respectTransparency false
open OAI.Analysis.DifferentialForms.Manifold.Bidegree

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [IsScalarTower ℝ ℂ V]

def antiholomorphicOneCovector (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 0 1 a) :
    V →ₗ⋆[ℂ] ℂ :=
  let D := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℂ) (0 : Fin 1)).symm a
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun z u => by
      by_cases hz : z = 0
      · simp only [hz, zero_smul, map_zero]
      · have h := ha (Units.mk0 z hz) (fun _ => u)
        change D (z • u) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 (Units.mk0 z hz) * D u at h
        simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0, pow_one, pow_zero, one_mul,
          smul_eq_mul, starRingEnd_apply] using h }

omit [IsScalarTower ℝ ℂ V] in
theorem antiholomorphicOneCovector_apply (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 0 1 a) (v : V) :
    antiholomorphicOneCovector a ha v = a (fun _ => v) := rfl

omit [IsScalarTower ℝ ℂ V] in
theorem antiholomorphicOneCovector_reconstruct (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 0 1 a) (v : Fin 1 → V) :
    antiholomorphicOneCovector a ha (v 0) = a v := by
  rw [antiholomorphicOneCovector_apply]
  congr 1
  exact funext (fun i => congrArg v (Subsingleton.elim 0 i))

theorem exists_hermitian_antiholomorphic_covector [FiniteDimensional ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hsym : ∀ a b, H b a = star (H a b))
    (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re)
    (ω : Analysis.DifferentialForms.Manifold.Basic.FormValue V 1) (hω : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 0 1 ω) :
    ∃ a : V, ∀ v : Fin 1 → V, ω v = (Real.pi : ℂ) * H (v 0) a := by
  obtain ⟨a, ha⟩ := HermitianAntiDual.exists_hermitian_antilinear_representative H hsym hpos
    ((Real.pi : ℂ)⁻¹ • antiholomorphicOneCovector ω hω)
  refine ⟨a, fun v => ?_⟩
  rw [ha]
  change ω v = (Real.pi : ℂ) * ((Real.pi : ℂ)⁻¹ * antiholomorphicOneCovector ω hω (v 0))
  rw [antiholomorphicOneCovector_reconstruct, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul]

end

end OAI.RepresentationTheory.Theta.Geometric.HermitianAntiholomorphicCovectors
