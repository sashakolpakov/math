import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Tensor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor

noncomputable section

/-!
# The tensor complex of commuting coordinate derivatives

For commuting linear operators, tensoring their coefficients with exterior
powers gives the coordinate de Rham differential. Its square vanishes by
pairwise cancellation and alternating multiplication, over any base ring.
-/

open scoped TensorProduct

universe u

theorem sum_sum_skew {ι N : Type*} [Fintype ι] [AddCommGroup N] (f : ι → ι → N)
    (hdiag : ∀ i, f i i = 0) (hskew : ∀ i j, f i j + f j i = 0) :
    ∑ i, ∑ j, f i j = 0 := by
  classical
  refine (Fintype.sum_prod_type (fun p : ι × ι => f p.1 p.2)).symm.trans ?_
  apply Finset.sum_ninvolution Prod.swap
  · intro p
    exact hskew p.1 p.2
  · rintro ⟨i, j⟩ hne heq
    have hji : j = i := congrArg Prod.fst heq
    subst j
    exact hne (hdiag i)
  · intro p
    exact Finset.mem_univ p.swap
  · intro p
    rfl

variable (R σ M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

abbrev Term (n : ℕ) := M ⊗[R] (⋀[R]^n (σ →₀ R))

def exteriorWedge (i : σ) (n : ℕ) : (⋀[R]^n (σ →₀ R)) →ₗ[R] (⋀[R]^(n + 1) (σ →₀ R)) :=
  ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single i 1) n

variable (D : σ → Module.End R M)

def differential (n : ℕ) : Term R σ M n →ₗ[R] Term R σ M (n + 1) :=
  ∑ i, TensorProduct.map (D i) (exteriorWedge R σ i n)

theorem differential_tmul (n : ℕ) (m : M) (ω : ⋀[R]^n (σ →₀ R)) :
    differential R σ M D n (m ⊗ₜ[R] ω) = ∑ i, D i m ⊗ₜ[R] exteriorWedge R σ i n ω := by
  simp only [differential, LinearMap.sum_apply, TensorProduct.map_tmul]

variable (hcomm : ∀ i j, Function.Commute (D i) (D j))

include hcomm in
theorem differential_square_linear (n : ℕ) :
    (differential R σ M D (n + 1)).comp (differential R σ M D n) = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  change differential R σ M D (n + 1) (differential R σ M D n (m ⊗ₜ[R] ω)) = 0
  rw [differential_tmul, map_sum]
  simp only [differential_tmul]
  apply sum_sum_skew
  · intro i
    change D i (D i m) ⊗ₜ[R]
      ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single i 1) (n + 1)
        (ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single i 1) n ω) = 0
    rw [ExteriorContractionCoe.ExteriorContraction.wedge_square, TensorProduct.tmul_zero]
  · intro i j
    rw [hcomm j i m, ← TensorProduct.tmul_add]
    change D i (D j m) ⊗ₜ[R]
      (ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single j 1) (n + 1)
        (ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single i 1) n ω) +
       ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single i 1) (n + 1)
        (ExteriorContractionCoe.ExteriorContraction.wedge R (σ →₀ R) (Finsupp.single j 1) n ω)) = 0
    rw [ExteriorContractionCoe.ExteriorContraction.wedge_anticommute, TensorProduct.tmul_zero]

/-- The cochain complex defined by the commuting coordinate operators. -/
def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (Term R σ M n))
    (fun n => ModuleCat.ofHom (differential R σ M D n))
    (fun n => ModuleCat.hom_ext (differential_square_linear R σ M D hcomm n))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor
