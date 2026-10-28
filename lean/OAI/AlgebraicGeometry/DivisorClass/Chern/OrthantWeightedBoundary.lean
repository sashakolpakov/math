import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

/-! # Orthant Weighted Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantWeightedBoundary

noncomputable section

/-! Boundary of an oriented orthant family whose internal faces cancel. -/

open OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem orthantWeighted_sum_zero {m : ℕ} {M : Type*} [AddCommGroup M]
    (i : Fin m) (f : (Fin m → Bool) → M) (hf : ∀ ε, f (OrthantSphereEquator.orthantFlip i ε) = f ε) :
    (∑ ε : Fin m → Bool, OrthantSphereEquator.orthantWeight ε • f ε) = 0 := by
  classical
  apply Finset.sum_ninvolution (OrthantSphereEquator.orthantFlip i)
  · intro ε
    rw [OrthantSphereEquator.orthantWeight_flip, hf, neg_zsmul, add_neg_cancel]
  · intro ε _
    exact OrthantSphereEquator.orthantFlip_ne i ε
  · intro ε
    exact Finset.mem_univ _
  · exact OrthantSphereEquator.orthantFlip_involutive i

theorem integer_smul_finite_sum {ι M : Type*} [Fintype ι] [AddCommGroup M]
    (a : ℤ) (f : ι → M) : a • ∑ i, f i = ∑ i, a • f i :=
  map_sum (zsmulAddGroupHom a) f Finset.univ

/-- Only the first face remains when all other faces are paired by
the explicit sign-flip involution. -/
theorem orthantWeighted_boundary_first (K : SSet.{0}) (n : ℕ)
    (s : (Fin (n + 1) → Bool) → K _⦋n + 1⦌)
    (hs : ∀ η i, K.δ i.succ (s (OrthantSphereEquator.orthantFlip i η)) = K.δ i.succ (s η)) :
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).d (n + 1) n
      (∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K (s η)) =
      ∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K (K.δ 0 (s η)) := by
  rw [map_sum]
  simp only [map_zsmul, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary]
  simp_rw [integer_smul_finite_sum]
  rw [Finset.sum_comm, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  have hother : (∑ i : Fin (n + 1), ∑ η : Fin (n + 1) → Bool,
      OrthantSphereEquator.orthantWeight η • (((-1 : ℤ) ^ i.succ.val) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K (K.δ i.succ (s η)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply orthantWeighted_sum_zero i
    intro η
    rw [hs]
  rw [hother, add_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantWeightedBoundary
