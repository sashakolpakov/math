import OAI.AlgebraicTopology.DeRham.Comparison.BidegreeRestriction
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

/-! # Top Bidegree -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.TopBidegree

/-!
# Top real covectors on complex tangent spaces

This file relates top-degree alternating covectors to actual determinants.
It is local linear algebra, with no Hodge decomposition or cohomology assumed.
-/

/-- An off-diagonal bidegree character cannot be the balanced real Jacobian
character. Differentiation along `1 + t I` detects the difference of degrees. -/
theorem bidegreeCharacter_eq_normSq_forall_imp_eq (p q k : ℕ)
    (h : ∀ z : ℂˣ, OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z =
      ((Complex.normSq (z : ℂ) ^ k : ℝ) : ℂ)) : p = q := by
  have hz (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
  have hf : (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) =
      (fun t : ℝ => (((1 + t ^ 2) ^ k : ℝ) : ℂ)) := by
    funext t
    have ht := h (Units.mk0 ((1 : ℂ) + (t : ℂ) * Complex.I) (hz t))
    have hn : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
      simpa using Complex.normSq_add_mul_I 1 t
    simpa [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Complex.star_def, hn,
      sub_eq_add_neg, mul_neg] using ht
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hplus : HasDerivAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I)
      Complex.I 0 := by
    simpa using (hr.mul_const Complex.I).const_add 1
  have hminus : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I)
      (-Complex.I) 0 := by
    simpa using (hr.mul_const Complex.I).const_sub 1
  have hleft : HasDerivAt (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q)
      (((p : ℂ) - (q : ℂ)) * Complex.I) 0 := by
    apply HasDerivAt.congr_deriv ((hplus.pow p).mul (hminus.pow q))
    norm_num
    ring
  have hright : HasDerivAt (fun t : ℝ => (((1 + t ^ 2) ^ k : ℝ) : ℂ))
      (0 : ℂ) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).pow 2).const_add 1).pow k).ofReal_comp
  rw [hf] at hleft
  have hd := hleft.unique hright
  have hc : (p : ℂ) = (q : ℂ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right Complex.I_ne_zero)
  exact_mod_cast hc

section TopForms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A complex-valued top covector is determined by its value on a real basis. -/
theorem topAlternating_eq_det_smul
    (b : Module.Basis ι ℝ V) (ω : V [⋀^ι]→ₗ[ℝ] ℂ) :
    ω = b.det.smulRight (ω b) := by
  apply b.ext_alternating
  intro v hv
  let σ : Equiv.Perm ι := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
  change ω (b ∘ σ) = (b.det.smulRight (ω b)) (b ∘ σ)
  simp [AlternatingMap.map_perm, Module.Basis.det_self]

/-- Top covectors transform by the real determinant. -/
theorem topAlternating_comp_apply
    (b : Module.Basis ι ℝ V) (ω : V [⋀^ι]→ₗ[ℝ] ℂ)
    (f : V →ₗ[ℝ] V) (v : ι → V) :
    ω (f ∘ v) = f.det • ω v := by
  rw [topAlternating_eq_det_smul b ω]
  simp only [AlternatingMap.smulRight_apply, Module.Basis.det_comp]
  rw [mul_smul]

end TopForms

section ComplexTopForms

variable {V : Type*} [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

/-- Simultaneous complex scalar multiplication on a real top covector acts
by the real Jacobian, the appropriate power of the squared complex norm. -/
theorem topAlternating_complex_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (ω : V [⋀^ι]→ₗ[ℝ] ℂ)
    (z : ℂ) (v : ι → V) :
    ω (fun i => z • v i) =
      (Complex.normSq z ^ Module.finrank ℂ V) • ω v := by
  have h := topAlternating_comp_apply b ω
    ((z • (LinearMap.id : V →ₗ[ℂ] V)).restrictScalars ℝ) v
  change ω (fun i => z • v i) =
    ((z • (LinearMap.id : V →ₗ[ℂ] V)).restrictScalars ℝ).det • ω v at h
  simpa only [LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow] using h

variable [FiniteDimensional ℂ V]

/-- Every real top-degree covector on a complex `k`-space has the actual
scalar-pullback character of bidegree `(k,k)`. -/
theorem topContinuousAlternating_hasBidegree {k : ℕ}
    (hk : Module.finrank ℂ V = k)
    (ω : V [⋀^Fin (k + k)]→L[ℝ] ℂ) : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V k k ω := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  have hr : Module.finrank ℝ V = k + k := by
    rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex, hk, two_mul]
  let b : Module.Basis (Fin (k + k)) ℝ V :=
    (Module.finBasis ℝ V).reindex (finCongr hr)
  intro z v
  have hc : OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter k k z = ((Complex.normSq (z : ℂ) ^ k : ℝ) : ℂ) := by
    rw [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, ← mul_pow, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_pow]
  rw [hc]
  simpa only [hk, Complex.real_smul, ContinuousAlternatingMap.coe_toAlternatingMap] using
    topAlternating_complex_smul b ω.toAlternatingMap (z : ℂ) v

/-- A top-degree covector of unequal complex degrees vanishes on a complex
tangent space. This is the local type statement for integration over that space. -/
theorem topContinuousAlternating_eq_zero_of_offDiagonal
    {p q : ℕ} (ω : V [⋀^Fin (p + q)]→L[ℝ] ℂ)
    (hω : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V p q ω)
    (hdim : p + q = 2 * Module.finrank ℂ V) (hpq : p ≠ q) : ω = 0 := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  have hr : Module.finrank ℝ V = p + q := by
    rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex, ← hdim]
  let b : Module.Basis (Fin (p + q)) ℝ V :=
    (Module.finBasis ℝ V).reindex (finCongr hr)
  ext v
  change ω v = 0
  by_contra hv
  apply hpq
  apply bidegreeCharacter_eq_normSq_forall_imp_eq p q (Module.finrank ℂ V)
  intro z
  apply mul_right_cancel₀ hv
  calc
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * ω v = ω (fun i => (z : ℂ) • v i) := (hω z v).symm
    _ = ((Complex.normSq (z : ℂ) ^ Module.finrank ℂ V : ℝ) : ℂ) * ω v := by
      simpa only [Complex.real_smul, ContinuousAlternatingMap.coe_toAlternatingMap] using
        topAlternating_complex_smul b ω.toAlternatingMap (z : ℂ) v

end ComplexTopForms

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]

/-- Pullback to a complex tangent space kills an off-diagonal pure covector
whose total degree is the real dimension of that tangent space. -/
theorem pureBidegree_pullback_eq_zero_of_offDiagonal_top
    {p q : ℕ} {ω : E [⋀^Fin (p + q)]→L[ℝ] ℂ}
    (hω : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q ω) (j : F →L[ℂ] E)
    (hdim : p + q = 2 * Module.finrank ℂ F) (hpq : p ≠ q) :
    ω.compContinuousLinearMap (j.restrictScalars ℝ) = 0 :=
  topContinuousAlternating_eq_zero_of_offDiagonal _
    (BidegreeRestriction.hasBidegree_pullback hω j) hdim hpq

end OAI.AlgebraicTopology.DeRham.Comparison.TopBidegree
