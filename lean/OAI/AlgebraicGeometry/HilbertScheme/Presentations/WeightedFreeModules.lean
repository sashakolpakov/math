import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BasisGrading
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Module.GradedModule

/-! # Weighted Free Modules -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFreeModules.GradedModules

noncomputable section

/-! Weighted free polynomial modules and their actual integer gradings. -/

open _root_.Module _root_.MvPolynomial

universe u v w

variable {σ : Type u} {ι : Type v} (R : Type w) [CommRing R]

def polynomialIntegerGrading : ℤ → Submodule R (MvPolynomial σ R) :=
  weightedHomogeneousSubmodule R (fun _ : σ => (1 : ℤ))

instance polynomialIntegerGradedAlgebra : GradedAlgebra (polynomialIntegerGrading (σ := σ) R) :=
  weightedGradedAlgebra R (fun _ : σ => (1 : ℤ))

def freeMonomialBasis : Basis (Σ _ : ι, σ →₀ ℕ) R (ι →₀ MvPolynomial σ R) :=
  Finsupp.basis (fun _ : ι => basisMonomials σ R)

def freeMonomialDegree (w : ι → ℤ) (p : Σ _ : ι, σ →₀ ℕ) : ℤ :=
  Finsupp.weight (fun _ : σ => (1 : ℤ)) p.2 + w p.1

def weightedFreeGrading (w : ι → ℤ) : ℤ → Submodule R (ι →₀ MvPolynomial σ R) :=
  BasisGrading.GradedModules.basisPiece (freeMonomialBasis (σ := σ) R) (freeMonomialDegree w)

instance weightedFreeDecomposition (w : ι → ℤ) :
    DirectSum.Decomposition (weightedFreeGrading (σ := σ) R w) :=
  BasisGrading.GradedModules.basisPieceDecomposition _ _

theorem mem_weightedFreeGrading (w : ι → ℤ) (d : ℤ) (f : ι →₀ MvPolynomial σ R) :
    f ∈ weightedFreeGrading R w d ↔ ∀ i, f i ∈ polynomialIntegerGrading R (d - w i) := by
  rw [weightedFreeGrading, BasisGrading.GradedModules.mem_basisPiece_iff]
  constructor
  · intro h i m hm
    have he : Finsupp.weight (fun _ : σ => (1 : ℤ)) m + w i = d := by
      by_contra hn
      exact hm (h ⟨i, m⟩ hn)
    omega
  · intro h p hp
    change AddMonoidAlgebra.coeff ((f p.1)) (p.2) = 0
    by_contra hn
    have he := h p.1 hn
    apply hp
    change Finsupp.weight (fun _ : σ => (1 : ℤ)) p.2 + w p.1 = d
    omega

instance weightedFreeGradedSMul (w : ι → ℤ) :
    SetLike.GradedSMul (polynomialIntegerGrading (σ := σ) R) (weightedFreeGrading (σ := σ) R w) where
  smul_mem := by
    intro n d a f ha hf
    rw [mem_weightedFreeGrading] at hf ⊢
    intro i
    have h := ha.mul (hf i)
    change IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (a * f i) (n + d - w i)
    have he : n + d - w i = n + (d - w i) := by omega
    rw [he]
    exact h

theorem weightedFree_single_homogeneous (w : ι → ℤ) (i : ι) :
    Finsupp.single i (1 : MvPolynomial σ R) ∈ weightedFreeGrading R w (w i) := by
  classical
  rw [mem_weightedFreeGrading]
  intro j
  by_cases h : i = j
  · subst j
    simp only [Finsupp.single_eq_same, sub_self]
    exact SetLike.GradedOne.one_mem
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    exact Submodule.zero_mem _

variable {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (polynomialIntegerGrading (σ := σ) R) ℳ]

omit [IsScalarTower R (MvPolynomial σ R) M] in
theorem weightedFree_linearCombination_homogeneous (w : ι → ℤ) (v : ι → M)
    (hv : ∀ i, v i ∈ ℳ (w i)) (d : ℤ) (f : ι →₀ MvPolynomial σ R)
    (hf : f ∈ weightedFreeGrading R w d) :
    Finsupp.linearCombination (MvPolynomial σ R) v f ∈ ℳ d := by
  change (∑ i ∈ f.support, f i • v i) ∈ ℳ d
  apply Submodule.sum_mem
  intro i _
  have h := SetLike.GradedSMul.smul_mem ((mem_weightedFreeGrading R w d f).mp hf i) (hv i)
  have he : (d - w i) + w i = d := sub_add_cancel _ _
  exact he ▸ h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFreeModules.GradedModules
