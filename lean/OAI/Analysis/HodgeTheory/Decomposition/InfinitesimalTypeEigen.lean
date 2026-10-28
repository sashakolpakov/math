import OAI.Analysis.HodgeTheory.Decomposition.MetricPullbackCurve
import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import OAI.Analysis.HodgeTheory.Decomposition.Projectors

/-! # Infinitesimal Type Eigen -/

namespace OAI.Analysis.HodgeTheory.Decomposition.InfinitesimalTypeEigen.Constructions

noncomputable section

section

/-! Genuine bidegrees are eigenspaces of infinitesimal complex rotation,
as follows by differentiating their full scalar character. -/

theorem complexRotationPerturbation_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem complexRotationCharacter_hasDerivAt (p q : ℕ) :
    HasDerivAt (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) (Complex.I * ((p : ℂ) - (q : ℂ))) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hp := ((ht.mul_const Complex.I).const_add (1 : ℂ)).pow p
  have hq := ((hasDerivAt_const (0 : ℝ) (1 : ℂ)).sub (ht.mul_const Complex.I)).pow q
  convert! hp.mul hq using 1
  norm_num
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

theorem tangentComplexRotationPerturbation (t : ℝ) (v : E) :
    MetricPullbackCurve.Constructions.tangentLinearPerturbation (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) t v =
      ((1 : ℂ) + (t : ℂ) * Complex.I) • v := by
  change v + t • (Complex.I • v) = ((1 : ℂ) + (t : ℂ) * Complex.I) • v
  rw [add_smul, one_smul, mul_smul]
  exact congrArg (fun w : E => v + w) (algebraMap_smul ℂ t (Complex.I • v)).symm

theorem pureCovector_rotation_curve (p q : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue E (p + q))
    (ha : DifferentialForms.Manifold.Bidegree.HasBidegree E p q a) (t : ℝ) :
    a.compContinuousLinearMap (MetricPullbackCurve.Constructions.tangentLinearPerturbation (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) t) =
      (((1 : ℂ) + (t : ℂ) * Complex.I) ^ p * ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) • a := by
  ext v
  change a (fun i => MetricPullbackCurve.Constructions.tangentLinearPerturbation (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) t (v i)) = _
  simp only [tangentComplexRotationPerturbation]
  change a (fun i => ((1 : ℂ) + (t : ℂ) * Complex.I) • v i) =
    (((1 : ℂ) + (t : ℂ) * Complex.I) ^ p * ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) * a v
  have h := ha (Units.mk0 ((1 : ℂ) + (t : ℂ) * Complex.I) (complexRotationPerturbation_ne_zero t)) v
  simpa only [Units.val_mk0, DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Complex.star_def, map_add, map_mul, map_one,
    Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg] using h

theorem covectorInfinitesimalRotation_pure (p q : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue E (p + q))
    (ha : DifferentialForms.Manifold.Bidegree.HasBidegree E p q a) :
    CovectorConnection.Constructions.covectorInfinitesimalAction (p + q) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a =
      (Complex.I * ((p : ℂ) - (q : ℂ))) • a := by
  have hleft := MetricPullbackCurve.Constructions.covectorPullback_hasDerivAt (p + q) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a
  have hright := (complexRotationCharacter_hasDerivAt p q).smul_const a
  have heq : (fun t => a.compContinuousLinearMap
      (MetricPullbackCurve.Constructions.tangentLinearPerturbation (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) t)) =
      (fun t : ℝ => (((1 : ℂ) + (t : ℂ) * Complex.I) ^ p * ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) • a) :=
    funext (pureCovector_rotation_curve p q a ha)
  rw [heq] at hleft
  exact hleft.unique hright

end

/-! Infinitesimal complex rotation has distinct eigenvalues on the genuine
bidegrees of any fixed total degree. -/

def typeRotationEigenvalue {n : ℕ} (i : Core.Constructions.Bidegree n) : ℂ :=
  Complex.I * ((i.val.1 : ℂ) - (i.val.2 : ℂ))

theorem typeRotationEigenvalue_injective (n : ℕ) : Function.Injective (@typeRotationEigenvalue n) := by
  intro i j h
  have hc : (i.val.1 : ℂ) - (i.val.2 : ℂ) = (j.val.1 : ℂ) - (j.val.2 : ℂ) :=
    mul_left_cancel₀ Complex.I_ne_zero h
  have hz : (i.val.1 : ℤ) - (i.val.2 : ℤ) = (j.val.1 : ℤ) - (j.val.2 : ℤ) := by exact_mod_cast hc
  have hi := i.property
  have hj := j.property
  apply Subtype.ext
  apply Prod.ext <;> omega

end

end OAI.Analysis.HodgeTheory.Decomposition.InfinitesimalTypeEigen.Constructions
