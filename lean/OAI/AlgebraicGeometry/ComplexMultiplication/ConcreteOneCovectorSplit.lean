import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts

/-! # Concrete One Covector Split -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteOneCovectorSplit

noncomputable section

/-! # Complementary actual holomorphic and antiholomorphic one-covectors

The projection proofs are adapted from `Hodge.CM.OneFormProjection`.
They act on the actual continuous alternating covectors.
-/

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The actual complex-linear projection has type (1,0). -/
theorem oneCovector_holomorphic_projection (φ : E [⋀^Fin 1]→L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 ((1 / 2 : ℂ) • (φ - Complex.I •
      φ.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  obtain ⟨D, rfl⟩ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).surjective φ
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E ℂ D (z : ℂ) (v 0)

/-- The actual conjugate-linear projection has type (0,1). -/
theorem oneCovector_antiholomorphic_projection (φ : E [⋀^Fin 1]→L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 ((1 / 2 : ℂ) • (φ + Complex.I •
      φ.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  obtain ⟨D, rfl⟩ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).surjective φ
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, one_mul, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E ℂ D (z : ℂ) (v 0)

omit [IsScalarTower ℝ ℂ E] in
/-- A one-covector in both actual pure subspaces is zero. -/
theorem oneCovector_pure_disjoint :
    Disjoint (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0) (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 0 1) := by
  apply Submodule.disjoint_def.mpr
  intro φ hφ kφ
  ext v
  let i : ℂˣ := ⟨Complex.I, -Complex.I, by simp, by simp⟩
  have h10 : φ (fun j => Complex.I • v j) = Complex.I * φ v := by
    simpa only [i, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one] using hφ i v
  have h01 : φ (fun j => Complex.I • v j) = -Complex.I * φ v := by
    simpa only [i, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, one_mul,
      Complex.star_def, Complex.conj_I] using kφ i v
  have h : Complex.I * φ v + Complex.I * φ v = 0 := by
    calc
      _ = -Complex.I * φ v + Complex.I * φ v :=
        congrArg (fun w => w + Complex.I * φ v) (h10.symm.trans h01)
      _ = 0 := by rw [neg_mul, neg_add_cancel]
  have h2 : (2 : ℂ) * (Complex.I * φ v) = 0 := by
    simpa only [two_mul] using h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (by norm_num))).resolve_left
    Complex.I_ne_zero

/-- The two actual pure one-covector subspaces span all real one-covectors. -/
theorem oneCovector_pure_sup_top :
    Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0 ⊔ Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 0 1 = ⊤ := by
  apply top_unique
  intro φ _
  apply Submodule.mem_sup.mpr
  refine ⟨(1 / 2 : ℂ) • (φ - Complex.I •
      φ.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)),
    oneCovector_holomorphic_projection E φ,
    (1 / 2 : ℂ) • (φ + Complex.I •
      φ.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)),
    oneCovector_antiholomorphic_projection E φ, ?_⟩
  ext v
  change (1 / 2 : ℂ) * (φ v - Complex.I * φ (fun j => Complex.I • v j)) +
    (1 / 2 : ℂ) * (φ v + Complex.I * φ (fun j => Complex.I • v j)) = φ v
  ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteOneCovectorSplit
