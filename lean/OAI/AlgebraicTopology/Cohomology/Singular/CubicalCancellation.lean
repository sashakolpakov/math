import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalFaces
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Cubical Cancellation -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalCancellation

noncomputable section

/-!
# Cancellation of internal faces in permutation triangulation

Every internal face is shared by the permutations differing by the adjacent
transposition at that face. The two permutations have opposite signs. The
finite sum therefore cancels by a fixed-point-free involution, in the actual
smooth singular chain module and in the ordinary singular chain module.

There is no division by two and no assumption on torsion in the coefficients.
-/

open _root_.CategoryTheory Opposite
open scoped BigOperators Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

section Permutations

variable {α : Type} [DecidableEq α]

/-- Precomposing a permutation with a nontrivial transposition has no fixed point. -/
theorem swap_trans_perm_ne (p q : α) (hpq : p ≠ q) (σ : Equiv.Perm α) :
    (Equiv.swap p q).trans σ ≠ σ := by
  intro h
  have he := congrArg (fun τ : Equiv.Perm α => τ p) h
  have hqp : q = p := σ.injective (by
    simpa only [Equiv.trans_apply, Equiv.swap_apply_left] using he)
  exact hpq hqp.symm

variable [Fintype α]

/-- A transposition reverses the integer-valued permutation sign. -/
theorem sign_swap_trans_int (p q : α) (hpq : p ≠ q) (σ : Equiv.Perm α) :
    (Equiv.Perm.sign ((Equiv.swap p q).trans σ) : ℤ) =
      -(Equiv.Perm.sign σ : ℤ) := by
  rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hpq]
  simp

/-- An invariant family cancels after weighting by permutation signs. The
proof pairs terms by a transposition, and is valid with arbitrary additive
coefficients, including coefficients with two-torsion. -/
theorem signedPermutationSum_eq_zero_of_swap {A : Type*} [AddCommGroup A]
    (p q : α) (hpq : p ≠ q) (F : Equiv.Perm α → A)
    (hF : ∀ σ, F ((Equiv.swap p q).trans σ) = F σ) :
    ∑ σ : Equiv.Perm α, (Equiv.Perm.sign σ : ℤ) • F σ = 0 := by
  classical
  apply Finset.sum_ninvolution (fun σ => (Equiv.swap p q).trans σ)
  · intro σ
    rw [hF, sign_swap_trans_int p q hpq]
    simp
  · intro σ _
    exact swap_trans_perm_ne p q hpq σ
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    ext x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]

end Permutations

variable {n m : ℕ}

/-- Adjacent permutation simplices have the same internal face as elements
of the genuine smooth singular simplicial set. -/
theorem triangulatedCubeSmoothSimplex_adjacentInternalFace
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (p q : Fin (n + 1))
    (hq : q.val = p.val + 1) :
    (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ q.castSucc
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ) =
      (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ q.castSucc
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube ((Equiv.swap p q).trans σ)) := by
  apply Subtype.ext
  change (TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).δ q.castSucc
      (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ).val =
    (TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).δ q.castSucc
      (CubicalTriangulation.triangulatedCubeSmoothSimplex cube ((Equiv.swap p q).trans σ)).val
  apply (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of (Fin m → ℝ)) n).injective
  rw [ContinuousFormulas.singularSimplicesEquivContinuousMap_face, ContinuousFormulas.singularSimplicesEquivContinuousMap_face]
  change (CubicalTriangulation.triangulatedCubeSimplex cube σ).comp (ContinuousFormulas.standardSimplexFace q.castSucc) =
    (CubicalTriangulation.triangulatedCubeSimplex cube ((Equiv.swap p q).trans σ)).comp
      (ContinuousFormulas.standardSimplexFace q.castSucc)
  apply ContinuousMap.ext
  intro w
  apply congrArg cube.toFun
  exact CubicalFaces.cubeSimplexLinearMap_adjacentSwap σ p q hq
    (Convexity.StdSimplex.map q.castSucc.succAbove w)
    (CubicalFaces.standardSimplexFace_omitted_coordinate q.castSucc w)

variable {R : Type} [Ring R]

/-- The actual smooth singular chain contributed by one face of one permutation
simplex, with an arbitrary coefficient value. -/
def smoothCubeFaceChain (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2)) (a : M) :
    (Smooth.smoothSingularChains M (Fin m → ℝ)).X n :=
  ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex (R := M)
    ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ k
      (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ))) a

/-- Equality of adjacent internal faces holds in the actual chain module. -/
theorem smoothCubeFaceChain_adjacentSwap (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (p q : Fin (n + 1))
    (hq : q.val = p.val + 1) (a : M) :
    smoothCubeFaceChain M cube σ q.castSucc a =
      smoothCubeFaceChain M cube ((Equiv.swap p q).trans σ) q.castSucc a := by
  unfold smoothCubeFaceChain
  rw [triangulatedCubeSmoothSimplex_adjacentInternalFace cube σ p q hq]

/-- Interior simplex-face indices for a cube of dimension `n+1`. The first
and last faces are the only excluded indices. -/
def cubeInternalFaceIndices (n : ℕ) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun k => 0 < k.val ∧ k.val < n + 1)

/-- The total signed internal-face contribution of permutation triangulation,
formed in the actual smooth singular chain module. -/
def smoothCubeInternalBoundaryChain (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) (a : M) :
    (Smooth.smoothSingularChains M (Fin m → ℝ)).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ k ∈ cubeInternalFaceIndices n,
    (Equiv.Perm.sign σ : ℤ) • ((-1 : ℤ) ^ k.val • smoothCubeFaceChain M cube σ k a)

/-- All internal faces cancel, in every positive cube dimension and over
arbitrary module coefficients. In dimension one the internal index set is empty. -/
theorem smoothCubeInternalBoundaryChain_eq_zero (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) (a : M) :
    smoothCubeInternalBoundaryChain M cube a = 0 := by
  classical
  unfold smoothCubeInternalBoundaryChain
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : 0 < k.val ∧ k.val < n + 1 := (Finset.mem_filter.mp hk).2
  let p : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  let q : Fin (n + 1) := ⟨k.val, hk'.2⟩
  have hq : q.val = p.val + 1 := by dsimp [p, q]; omega
  have hpq : p ≠ q := by
    intro h
    have he := congrArg Fin.val h
    dsimp [p, q] at he
    omega
  have hqk : q.castSucc = k := by apply Fin.ext; rfl
  apply signedPermutationSum_eq_zero_of_swap p q hpq
  intro σ
  rw [← hqk, ← smoothCubeFaceChain_adjacentSwap M cube σ p q hq a]

/-- The same face regarded in the ordinary continuous singular chain module. -/
def cubeFaceChain (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2)) (a : M) :
    ((TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).chainComplex M).X n :=
  ((TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).ιChainComplex (R := M)
    ((TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).δ k
      (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ).val)) a

/-- Inclusion of smooth singular chains carries each actual face generator to
the corresponding ordinary singular face generator. -/
theorem smoothSingularChainInclusion_cubeFaceChain (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2)) (a : M) :
    (Smooth.smoothSingularChainInclusion M (Fin m → ℝ)).f n
        (smoothCubeFaceChain M cube σ k a) = cubeFaceChain M cube σ k a := by
  exact ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet
      (TopCat.toSSet.obj (TopCat.of (Fin m → ℝ)))
      (Smooth.smoothSingularInclusion (Fin m → ℝ)) M
      ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ k
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ))) a

/-- The signed internal-face sum in the ordinary singular chain module. -/
def cubeInternalBoundaryChain (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) (a : M) :
    ((TopCat.toSSet.obj (TopCat.of (Fin m → ℝ))).chainComplex M).X n :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ k ∈ cubeInternalFaceIndices n,
    (Equiv.Perm.sign σ : ℤ) • ((-1 : ℤ) ^ k.val • cubeFaceChain M cube σ k a)

/-- All internal faces also cancel in the actual ordinary singular chain module. -/
theorem cubeInternalBoundaryChain_eq_zero (M : ModuleCat.{0} R)
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) (a : M) :
    cubeInternalBoundaryChain M cube a = 0 := by
  have h := congrArg ((Smooth.smoothSingularChainInclusion M (Fin m → ℝ)).f n)
    (smoothCubeInternalBoundaryChain_eq_zero M cube a)
  simpa only [smoothCubeInternalBoundaryChain, cubeInternalBoundaryChain,
    map_sum, map_zsmul, map_zero, smoothSingularChainInclusion_cubeFaceChain] using h

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalCancellation
