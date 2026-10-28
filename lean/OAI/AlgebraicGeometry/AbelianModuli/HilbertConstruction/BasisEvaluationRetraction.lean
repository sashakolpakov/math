import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitEvaluationCokernel

/-! # Basis Evaluation Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationRetraction

noncomputable section

/-! A left inverse of the evaluation matrix constructs a left inverse
of the evaluation map itself, using the chosen basis. -/
universe u v w z
variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {V : Type z} [AddCommGroup V] [Module R V]

theorem linearEvaluation_leftInverse_of_basisMatrix
    (b : Module.Basis ν R V) (ev : V →ₗ[R] (ι → R))
    (B : Matrix ν ι R) (hB : B * BasisEvaluationMatrices.basisEvaluationMatrix b ev = 1) :
    ∃ g : (ι → R) →ₗ[R] V, g.comp ev = LinearMap.id := by
  let g := b.equivFun.symm.toLinearMap.comp (Matrix.toLin' B)
  have hlin : (Matrix.toLin' B).comp (Matrix.toLin' (BasisEvaluationMatrices.basisEvaluationMatrix b ev)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hB, Matrix.toLin'_one]
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun hlin (b.equivFun x)
  rw [BasisEvaluationMatrices.basisEvaluationMatrix_linearMap] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.id_apply] at h
  change b.equivFun.symm (Matrix.toLin' B (ev x)) = x
  rw [h, LinearEquiv.symm_apply_apply]

theorem linearEvaluation_projective_cokernel_of_basisMatrix
    (b : Module.Basis ν R V) (ev : V →ₗ[R] (ι → R))
    (B : Matrix ν ι R) (hB : B * BasisEvaluationMatrices.basisEvaluationMatrix b ev = 1) :
    Module.Projective R ((ι → R) ⧸ ev.range) := by
  obtain ⟨g, hg⟩ := linearEvaluation_leftInverse_of_basisMatrix b ev B hB
  exact SplitEvaluationCokernel.projective_cokernel_of_leftInverse ev g hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationRetraction
