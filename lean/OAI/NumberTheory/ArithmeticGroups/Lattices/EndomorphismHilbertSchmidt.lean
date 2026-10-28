import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.HilbertSchmidt
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Endomorphism Hilbert Schmidt -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.EndomorphismHilbertSchmidt.Construction

noncomputable section

section

/-! Euclidean coordinates and the Hilbert--Schmidt inner product
on endomorphisms. The commutator action respects adjoints. -/

open _root_.ContinuousLinearMap

def pairUncurryLinearEquiv (k ι : Type*) [Field k] : (ι → ι → k) ≃ₗ[k] (ι × ι → k) where
  toFun f p := f p.1 p.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

local instance hsEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance hsEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance hsEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def continuousEndEuclideanCoordinates (b : Module.Basis ι ℝ L) :
    (L →L[ℝ] L) ≃L[ℝ] EuclideanSpace ℝ (ι × ι) :=
  (((((LinearMap.toContinuousLinearMap : (L →ₗ[ℝ] L) ≃ₗ[ℝ] (L →L[ℝ] L)).symm.trans
    (b.constr ℝ).symm).trans (LinearEquiv.piCongrRight fun _ => b.equivFun)).trans
    (pairUncurryLinearEquiv ℝ ι)).trans (WithLp.linearEquiv 2 ℝ (ι × ι → ℝ)).symm).toContinuousLinearEquiv

theorem continuousEndEuclideanCoordinates_apply (b : Module.Basis ι ℝ L)
    (A : L →L[ℝ] L) (i j : ι) :
    continuousEndEuclideanCoordinates b A (i, j) = b.equivFun (A (b i)) j := rfl

theorem continuousEndEuclideanCoordinates_inner (b : OrthonormalBasis ι ℝ L) (A C : L →L[ℝ] L) :
    inner ℝ (continuousEndEuclideanCoordinates b.toBasis A) (continuousEndEuclideanCoordinates b.toBasis C) =
      ∑ i, inner ℝ (A (b i)) (C (b i)) := by
  change (∑ p : ι × ι, continuousEndEuclideanCoordinates b.toBasis C p *
    continuousEndEuclideanCoordinates b.toBasis A p) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [continuousEndEuclideanCoordinates_apply, Module.Basis.equivFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
  exact b.repr.inner_map_map (A (b i)) (C (b i))

def continuousCommutatorRepresentation : (L →L[ℝ] L) →ₗ[ℝ]
    ((L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L)) :=
  (ContinuousLinearMap.mul ℝ (L →L[ℝ] L) - (ContinuousLinearMap.mul ℝ (L →L[ℝ] L)).flip).toLinearMap

omit [FiniteDimensional ℝ L] in
theorem continuousCommutatorRepresentation_apply (A X : L →L[ℝ] L) :
    continuousCommutatorRepresentation A X = A * X - X * A := rfl

omit [FiniteDimensional ℝ L] in
theorem continuousCommutatorRepresentation_commutator (A C : L →L[ℝ] L) :
    continuousCommutatorRepresentation (A * C - C * A) =
      continuousCommutatorRepresentation A * continuousCommutatorRepresentation C -
        continuousCommutatorRepresentation C * continuousCommutatorRepresentation A := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [sub_apply, mul_apply_eq_comp, continuousCommutatorRepresentation_apply]
  noncomm_ring

omit [FiniteDimensional ℝ L] in
theorem commutator_sum_inner [CompleteSpace L] (b : OrthonormalBasis ι ℝ L)
    (A X Y : L →L[ℝ] L) :
    (∑ i, inner ℝ ((A * X - X * A) (b i)) (Y (b i))) =
      ∑ i, inner ℝ (X (b i)) ((adjoint A * Y - Y * adjoint A) (b i)) := by
  have hleft : (∑ i, inner ℝ (A (X (b i))) (Y (b i))) =
      ∑ i, inner ℝ (X (b i)) (adjoint A (Y (b i))) :=
    Finset.sum_congr rfl (fun i _ => (adjoint_inner_right A _ _).symm)
  simp only [sub_apply, mul_apply_eq_comp, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  rw [hleft, Bilinear.HilbertSchmidt.Construction.orthonormal_sum_inner_precomp_adjoint b A X Y]

end

/-! The commutator representation in Euclidean endomorphism
coordinates preserves commutators and adjoints. -/

open _root_.ContinuousLinearMap

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

def euclideanCommutatorRepresentation (b : OrthonormalBasis ι ℝ L) :
    (L →L[ℝ] L) →ₗ[ℝ] (EuclideanSpace ℝ (ι × ι) →L[ℝ] EuclideanSpace ℝ (ι × ι)) :=
  (continuousEndEuclideanCoordinates b.toBasis).conjContinuousAlgEquiv.toAlgEquiv.toLinearMap.comp
    continuousCommutatorRepresentation

theorem euclideanCommutatorRepresentation_apply (b : OrthonormalBasis ι ℝ L)
    (A X : L →L[ℝ] L) :
    euclideanCommutatorRepresentation b A (continuousEndEuclideanCoordinates b.toBasis X) =
      continuousEndEuclideanCoordinates b.toBasis (A * X - X * A) := by
  change continuousEndEuclideanCoordinates b.toBasis
    (continuousCommutatorRepresentation A ((continuousEndEuclideanCoordinates b.toBasis).symm
      (continuousEndEuclideanCoordinates b.toBasis X))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, continuousCommutatorRepresentation_apply]

theorem euclideanCommutatorRepresentation_commutator (b : OrthonormalBasis ι ℝ L)
    (A C : L →L[ℝ] L) :
    euclideanCommutatorRepresentation b (A * C - C * A) =
      euclideanCommutatorRepresentation b A * euclideanCommutatorRepresentation b C -
        euclideanCommutatorRepresentation b C * euclideanCommutatorRepresentation b A := by
  change (continuousEndEuclideanCoordinates b.toBasis).conjContinuousAlgEquiv
    (continuousCommutatorRepresentation (A * C - C * A)) = _
  rw [continuousCommutatorRepresentation_commutator, map_sub, map_mul, map_mul]
  rfl

theorem euclideanCommutatorRepresentation_inner [CompleteSpace L] (b : OrthonormalBasis ι ℝ L)
    (A X Y : L →L[ℝ] L) :
    inner ℝ (euclideanCommutatorRepresentation b A (continuousEndEuclideanCoordinates b.toBasis X))
      (continuousEndEuclideanCoordinates b.toBasis Y) =
        inner ℝ (continuousEndEuclideanCoordinates b.toBasis X)
          (euclideanCommutatorRepresentation b (adjoint A) (continuousEndEuclideanCoordinates b.toBasis Y)) := by
  rw [euclideanCommutatorRepresentation_apply, euclideanCommutatorRepresentation_apply,
    continuousEndEuclideanCoordinates_inner, continuousEndEuclideanCoordinates_inner]
  exact commutator_sum_inner b A X Y

theorem euclideanCommutatorRepresentation_adjoint [CompleteSpace L] (b : OrthonormalBasis ι ℝ L)
    (A : L →L[ℝ] L) :
    euclideanCommutatorRepresentation b (adjoint A) = adjoint (euclideanCommutatorRepresentation b A) := by
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  obtain ⟨X, rfl⟩ := (continuousEndEuclideanCoordinates b.toBasis).surjective x
  obtain ⟨Y, rfl⟩ := (continuousEndEuclideanCoordinates b.toBasis).surjective y
  simpa only [adjoint_adjoint] using euclideanCommutatorRepresentation_inner b (adjoint A) X Y

theorem euclideanCommutatorRepresentation_isSymmetric [CompleteSpace L] (b : OrthonormalBasis ι ℝ L)
    (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric) :
    (euclideanCommutatorRepresentation b A).toLinearMap.IsSymmetric := by
  have he := euclideanCommutatorRepresentation_adjoint b A
  rw [hA.clm_adjoint_eq] at he
  exact (eq_adjoint_iff _ _).mp he

theorem euclideanCommutatorRepresentation_commute (b : OrthonormalBasis ι ℝ L)
    (A C : L →L[ℝ] L) (hAC : Commute A C) :
    Commute (euclideanCommutatorRepresentation b A).toLinearMap
      (euclideanCommutatorRepresentation b C).toLinearMap := by
  have he := euclideanCommutatorRepresentation_commutator b A C
  rw [sub_eq_zero.mpr hAC.eq, map_zero] at he
  have hm := congrArg ContinuousLinearMap.toLinearMap (sub_eq_zero.mp he.symm)
  exact hm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.EndomorphismHilbertSchmidt.Construction
