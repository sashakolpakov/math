import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric

/-! # Mixed Two Coefficient -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction

noncomputable section

/-! The mixed component of a genuine two-form is conjugate-linear in its
first tangent vector and complex-linear in its second tangent vector. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem twoFormBilinear_skew (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) :
    KahlerDifferential.CM.Construction.twoFormBilinear f v u = -KahlerDifferential.CM.Construction.twoFormBilinear f u v := by
  rw [KahlerDifferential.CM.Construction.twoFormBilinear_apply, KahlerDifferential.CM.Construction.twoFormBilinear_apply]
  have h := f.toAlternatingMap.map_swap ![u, v] (by decide : (0 : Fin 2) ≠ 1)
  have hv : ![u, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, u] := by
    ext i
    fin_cases i <;> simp
  rw [hv] at h
  exact h

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormBilinear_type11_J (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) (u v : E) :
    KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) (Complex.I • v) = KahlerDifferential.CM.Construction.twoFormBilinear f u v := by
  have h := hf Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricIUnit ![u, v]
  have hc : Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricIUnit = 1 := by
    simp [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricIUnit]
  rw [hc, one_mul] at h
  rw [KahlerDifferential.CM.Construction.twoFormBilinear_apply, KahlerDifferential.CM.Construction.twoFormBilinear_apply]
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormBilinear_type11_J_left (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) (u v : E) :
    KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) v = -KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v) := by
  have h := twoFormBilinear_type11_J f hf u (Complex.I • v)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

def mixedTwoCoefficient (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) : ℂ :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E →L[ℝ] ℂ) (KahlerDifferential.CM.Construction.twoFormBilinear f) u) v

theorem mixedTwoCoefficient_apply (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) :
    mixedTwoCoefficient f u v = (1 / 4 : ℂ) *
      (KahlerDifferential.CM.Construction.twoFormBilinear f u v + KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) (Complex.I • v) -
        Complex.I * KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v) +
        Complex.I * KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) v) := by
  simp only [mixedTwoCoefficient, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply,
    smul_apply, add_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem mixedTwoCoefficient_add_left (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v w : E) :
    mixedTwoCoefficient f (u + v) w = mixedTwoCoefficient f u w + mixedTwoCoefficient f v w := by
  simp only [mixedTwoCoefficient, map_add, add_apply]

theorem mixedTwoCoefficient_add_right (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v w : E) :
    mixedTwoCoefficient f u (v + w) = mixedTwoCoefficient f u v + mixedTwoCoefficient f u w := by
  exact (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E →L[ℝ] ℂ) (KahlerDifferential.CM.Construction.twoFormBilinear f) u)).map_add v w

theorem mixedTwoCoefficient_smul_left (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (z : ℂ) (u v : E) :
    mixedTwoCoefficient f (z • u) v = star z * mixedTwoCoefficient f u v := by
  simp only [mixedTwoCoefficient, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul, map_smul,
    smul_apply, smul_eq_mul]

theorem mixedTwoCoefficient_smul_right (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (z : ℂ) (u v : E) :
    mixedTwoCoefficient f u (z • v) = z * mixedTwoCoefficient f u v := by
  exact Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E ℂ _ z v

def mixedTwoSesquilinear (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := mixedTwoCoefficient f u
      map_add' := mixedTwoCoefficient_add_right f u
      map_smul' := fun z v => mixedTwoCoefficient_smul_right f z u v }
  map_add' u v := by ext w; exact mixedTwoCoefficient_add_left f u v w
  map_smul' z u := by ext v; exact mixedTwoCoefficient_smul_left f z u v

theorem mixedTwoCoefficient_type11 (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) (u v : E) :
    mixedTwoCoefficient f u v = (1 / 2 : ℂ) *
      (KahlerDifferential.CM.Construction.twoFormBilinear f u v - Complex.I * KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v)) := by
  rw [mixedTwoCoefficient_apply, twoFormBilinear_type11_J f hf, twoFormBilinear_type11_J_left f hf]
  ring

theorem mixedTwoCoefficient_type11_reconstruct (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) (u v : E) :
    KahlerDifferential.CM.Construction.twoFormBilinear f u v = mixedTwoCoefficient f u v - mixedTwoCoefficient f v u := by
  rw [mixedTwoCoefficient_type11 f hf, mixedTwoCoefficient_type11 f hf,
    twoFormBilinear_skew f (Complex.I • u) v, twoFormBilinear_type11_J_left f hf,
    twoFormBilinear_skew f u v]
  ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction
