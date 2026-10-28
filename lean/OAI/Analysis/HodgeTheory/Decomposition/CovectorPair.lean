import OAI.Analysis.HodgeTheory.Decomposition.Hermitian
import OAI.Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

/-! # Covector Pair -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions

noncomputable section

/-! Positive Hermitian pairings on the actual complex-valued real covectors.
The orthonormal-basis comparison below makes the construction intrinsic. -/

open scoped BigOperators

section Algebraic

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- The Hermitian pairing of covector coordinates in a real basis. -/
def covectorBasisPair (b : Module.Basis ι ℝ E) (f g : E →ₗ[ℝ] ℂ) : ℂ :=
  ∑ i, star (f (b i)) * g (b i)

theorem covectorBasisPair_symm (b : Module.Basis ι ℝ E) (f g : E →ₗ[ℝ] ℂ) :
    star (covectorBasisPair b g f) = covectorBasisPair b f g := by
  simp only [covectorBasisPair, star_sum, star_mul, star_star]

theorem covectorBasisPair_add_left (b : Module.Basis ι ℝ E) (f g h : E →ₗ[ℝ] ℂ) :
    covectorBasisPair b (f + g) h = covectorBasisPair b f h + covectorBasisPair b g h := by
  simp only [covectorBasisPair, LinearMap.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem covectorBasisPair_smul_left (b : Module.Basis ι ℝ E) (f g : E →ₗ[ℝ] ℂ) (z : ℂ) :
    covectorBasisPair b (z • f) g = star z * covectorBasisPair b f g := by
  simp only [covectorBasisPair, LinearMap.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem covectorBasisPair_self (b : Module.Basis ι ℝ E) (f : E →ₗ[ℝ] ℂ) :
    covectorBasisPair b f f = ((∑ i, Complex.normSq (f (b i)) : ℝ) : ℂ) := by
  simp only [covectorBasisPair, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

theorem covectorBasisPair_nonneg (b : Module.Basis ι ℝ E) (f : E →ₗ[ℝ] ℂ) :
    0 ≤ (covectorBasisPair b f f).re := by
  rw [covectorBasisPair_self, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (f (b i)))

theorem covectorBasisPair_definite (b : Module.Basis ι ℝ E) (f : E →ₗ[ℝ] ℂ)
    (hf : covectorBasisPair b f f = 0) : f = 0 := by
  have hsum : ∑ i, Complex.normSq (f (b i)) = 0 := by
    have h := congrArg Complex.re hf
    simpa only [covectorBasisPair_self, Complex.ofReal_re, Complex.zero_re] using h
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Complex.normSq_nonneg (f (b i)))).mp hsum
  apply b.ext
  intro i
  exact Complex.normSq_eq_zero.mp (hi i (Finset.mem_univ i))

/-- This is data for a Hilbert norm on the finite-dimensional covector space. -/
@[instance_reducible] def covectorHermitianCore (b : Module.Basis ι ℝ E) :
    InnerProductSpace.Core ℂ (E →ₗ[ℝ] ℂ) where
  inner := covectorBasisPair b
  conj_inner_symm f g := by
    change star (covectorBasisPair b g f) = _
    exact covectorBasisPair_symm b f g
  add_left := covectorBasisPair_add_left b
  smul_left := fun f g z => covectorBasisPair_smul_left b f g z
  re_inner_nonneg := covectorBasisPair_nonneg b
  definite := covectorBasisPair_definite b

end Algebraic

section Orthonormal

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

theorem linearCovector_basis_expansion (b : OrthonormalBasis ι ℝ E)
    (f : E →ₗ[ℝ] ℂ) (x : E) :
    f x = ∑ i, (inner ℝ (b i) x : ℂ) * f (b i) := by
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, Complex.real_smul]

/-- A sum over either real orthonormal basis gives the same Hermitian pairing. -/
theorem covectorBasisPair_orthonormal_independent
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (f g : E →ₗ[ℝ] ℂ) :
    covectorBasisPair b.toBasis f g = covectorBasisPair c.toBasis f g := by
  classical
  have hdelta (j k : ι) :
      ∑ i, (inner ℝ (b j) (c i) : ℂ) * (inner ℝ (b k) (c i) : ℂ) =
        if j = k then 1 else 0 := by
    have h := c.sum_inner_mul_inner (b j) (b k)
    rw [b.inner_eq_ite] at h
    have hc := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
      Complex.ofReal_one, Complex.ofReal_zero, real_inner_comm (c _) (b k)] using hc
  unfold covectorBasisPair
  simp only [OrthonormalBasis.coe_toBasis]
  conv_rhs =>
    enter [2, i]
    rw [linearCovector_basis_expansion b f (c i), linearCovector_basis_expansion b g (c i)]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hterm (k : ι) :
      (∑ i : κ, star (f (b k)) * (inner ℝ (b k) (c i) : ℂ) *
        ((inner ℝ (b j) (c i) : ℂ) * g (b j))) =
      (star (f (b k)) * g (b j)) * (if k = j then 1 else 0) := by
    rw [← hdelta k j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [← Complex.star_def, hterm]
  simp

end Orthonormal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The intrinsic Hermitian pairing on complex-valued real linear covectors. -/
def covectorInner (f g : E →ₗ[ℝ] ℂ) : ℂ :=
  covectorBasisPair (stdOrthonormalBasis ℝ E).toBasis f g

theorem covectorInner_eq_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f g : E →ₗ[ℝ] ℂ) : covectorInner f g = covectorBasisPair b.toBasis f g :=
  covectorBasisPair_orthonormal_independent (stdOrthonormalBasis ℝ E) b f g

/-- Real isometries preserve the complex-valued covector pairing under pullback. -/
theorem covectorInner_pullback_isometry (L : E ≃ₗᵢ[ℝ] F) (f g : F →ₗ[ℝ] ℂ) :
    covectorInner (f.comp L.toLinearEquiv.toLinearMap) (g.comp L.toLinearEquiv.toLinearMap) =
      covectorInner f g := by
  rw [covectorInner_eq_basis ((stdOrthonormalBasis ℝ E).map L) f g]
  rfl

theorem covectorInner_symm (f g : E →ₗ[ℝ] ℂ) : star (covectorInner g f) = covectorInner f g :=
  covectorBasisPair_symm _ f g

theorem covectorInner_nonneg (f : E →ₗ[ℝ] ℂ) : 0 ≤ (covectorInner f f).re :=
  covectorBasisPair_nonneg _ f

theorem covectorInner_definite (f : E →ₗ[ℝ] ℂ) (hf : covectorInner f f = 0) : f = 0 :=
  covectorBasisPair_definite _ f hf

end

end OAI.Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions
