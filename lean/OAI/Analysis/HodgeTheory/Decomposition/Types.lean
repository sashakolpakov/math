import OAI.Analysis.HodgeTheory.Decomposition.Core
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Types -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Types.Constructions

noncomputable section

/-! General independence of pure types on actual differential forms. -/

/-- The inverse-scalar representation on families of actual smooth forms. -/
def componentAction (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (z : ℂˣ) :
    Module.End ℂ (X.componentForms n) :=
  LinearMap.pi fun C =>
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z).comp (LinearMap.proj C)

@[simp]
theorem componentAction_apply (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (z : ℂˣ) (form : X.componentForms n) (C : irreducibleComponents X.carrier) :
    componentAction X n z form C = DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z (form C) := rfl

theorem componentAction_commute (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (z w : ℂˣ) :
    Commute (componentAction X n z) (componentAction X n w) := by
  apply LinearMap.ext
  intro form
  funext C
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction w (form C)) =
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction w (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z (form C))
  rw [← DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction_mul, ← DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction_mul, mul_comm z w]

/-- The character curve reads the signed degree by differentiation at the identity. -/
theorem character_curve_hasDerivAt (p q : ℕ) :
    HasDerivAt (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q)
      (((p : ℂ) - (q : ℂ)) * Complex.I) 0 := by
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hplus : HasDerivAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (hr.mul_const Complex.I).const_add 1
  have hminus : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I) (-Complex.I) 0 := by
    simpa using (hr.mul_const Complex.I).const_sub 1
  apply HasDerivAt.congr_deriv ((hplus.pow p).mul (hminus.pow q))
  norm_num
  ring

theorem character_signed_degree (p q r s : ℕ)
    (h : ∀ z : ℂˣ, DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z = DifferentialForms.Manifold.Bidegree.bidegreeCharacter r s z) :
    (p : ℤ) - q = (r : ℤ) - s := by
  have hz (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
  have he : (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) =
      (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ r *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ s) := by
    funext t
    have ht := h (Units.mk0 ((1 : ℂ) + (t : ℂ) * Complex.I) (hz t))
    simpa [DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Complex.star_def, sub_eq_add_neg, mul_neg] using ht
  have hd := character_curve_hasDerivAt p q
  rw [he] at hd
  have hc := mul_right_cancel₀ Complex.I_ne_zero
    (hd.unique (character_curve_hasDerivAt r s))
  exact_mod_cast hc

def inverseTypeCharacter {n : ℕ} (i : Core.Constructions.Bidegree n) (z : ℂˣ) : ℂ :=
  DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z⁻¹

theorem inverseTypeCharacter_injective (n : ℕ) :
    Function.Injective (@inverseTypeCharacter n) := by
  intro i j h
  have hc : ∀ z : ℂˣ, DifferentialForms.Manifold.Bidegree.bidegreeCharacter i.val.1 i.val.2 z =
      DifferentialForms.Manifold.Bidegree.bidegreeCharacter j.val.1 j.val.2 z := by
    intro z
    simpa only [inverseTypeCharacter, inv_inv] using congrFun h z⁻¹
  have hs := character_signed_degree i.val.1 i.val.2 j.val.1 j.val.2 hc
  have hi := i.property
  have hj := j.property
  apply Subtype.ext
  apply Prod.ext <;> omega

/-- Pure forms are exactly the simultaneous eigenspaces of the scalar action. -/
theorem pureFormsAt_eq_eigenspaces (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Core.Constructions.Bidegree n) :
    Core.Constructions.pureFormsAt X n i = ⨅ z : ℂˣ, (componentAction X n z).eigenspace
      (inverseTypeCharacter i z) := by
  ext form
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  rw [Core.Constructions.mem_pureFormsAt_iff_action]
  constructor
  · intro h z
    funext C
    simpa only [componentAction_apply, inverseTypeCharacter, DifferentialForms.Manifold.Bidegree.bidegreeCharacter_inv,
      Pi.smul_apply] using h C z
  · intro h C z
    simpa only [componentAction_apply, inverseTypeCharacter, DifferentialForms.Manifold.Bidegree.bidegreeCharacter_inv,
      Pi.smul_apply] using congrFun (h z) C

/-- Distinct bidegrees are independent as spaces of smooth differential forms. -/
theorem pureFormsAt_iSupIndep (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    iSupIndep (Core.Constructions.pureFormsAt X n) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (componentAction X n) (fun z w μ =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (componentAction_commute X n w z) μ)
  apply (h.comp (inverseTypeCharacter_injective n)).mono
  intro i
  rw [pureFormsAt_eq_eigenspaces]
  exact iInf_mono fun z => Module.End.eigenspace_le_maxGenEigenspace

end

end OAI.Analysis.HodgeTheory.Decomposition.Types.Constructions
