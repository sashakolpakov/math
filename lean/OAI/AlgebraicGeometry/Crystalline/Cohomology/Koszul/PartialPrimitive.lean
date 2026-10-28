import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy

/-! # Partial Primitive -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.PartialPrimitive.KoszulPartialPrimitive

noncomputable section

/-!
# Coordinate homotopies for partial primitives

An integration operator can leave residual coefficients in both degrees.
The existing null-homotopy construction has an explicit projection with
the two residual coefficient operators on the corresponding exterior
components. This applies when integration excludes weights divisible by p.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy

universe u

theorem tensor_split {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a b c : M) (x y z : N) (h : x + y = z) :
    b ⊗ₜ[R] x + c ⊗ₜ[R] y + ((a - b) ⊗ₜ[R] (z - y) + (a - c) ⊗ₜ[R] y) = a ⊗ₜ[R] z := by
  rw [← h, add_sub_cancel_right, TensorProduct.sub_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_add]
  abel

variable (R σ M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]
  (D : σ → Module.End R M) (i : σ) (S : Module.End R M)

def projectionOne : Module.End R M := LinearMap.id - (D i).comp S

def projection : (n : ℕ) → Module.End R (Tensor.KoszulTensor.Term R σ M n)
  | 0 => CoordinateHomotopy.KoszulCoordinateHomotopy.projectionMap R σ M D i S 0
  | n + 1 => CoordinateHomotopy.KoszulCoordinateHomotopy.projectionMap R σ M D i S (n + 1) +
      TensorProduct.map (projectionOne R σ M D i S)
        ((Tensor.KoszulTensor.exteriorWedge R σ i n).comp (CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i n))

variable (hcommS : ∀ j, j ≠ i → ∀ m, D j (S m) = S (D j m))

include hcommS in
theorem homotopy_succ (n : ℕ) :
    (CoordinateHomotopy.KoszulCoordinateHomotopy.homotopyMap R σ M i S (n + 1)).comp (Tensor.KoszulTensor.differential R σ M D (n + 1)) +
      (Tensor.KoszulTensor.differential R σ M D n).comp (CoordinateHomotopy.KoszulCoordinateHomotopy.homotopyMap R σ M i S n) +
        projection R σ M D i S (n + 1) = LinearMap.id := by
  classical
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  have hsum : (∑ j, (S (D j m) ⊗ₜ[R]
        CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ j (n + 1) ω) +
      D j (S m) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ j n (CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i n ω))) =
      S (D i m) ⊗ₜ[R] CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ i (n + 1) ω) +
        D i (S m) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ i n (CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i n ω) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hcommS j hji m, ← TensorProduct.tmul_add, CoordinateHomotopy.KoszulCoordinateHomotopy.contraction_wedge,
        Finsupp.single_eq_of_ne (Ne.symm hji), zero_smul, TensorProduct.tmul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  change CoordinateHomotopy.KoszulCoordinateHomotopy.homotopyMap R σ M i S (n + 1) (Tensor.KoszulTensor.differential R σ M D (n + 1) (m ⊗ₜ[R] ω)) +
    Tensor.KoszulTensor.differential R σ M D n (CoordinateHomotopy.KoszulCoordinateHomotopy.homotopyMap R σ M i S n (m ⊗ₜ[R] ω)) +
      projection R σ M D i S (n + 1) (m ⊗ₜ[R] ω) = m ⊗ₜ[R] ω
  rw [Tensor.KoszulTensor.differential_tmul, map_sum]
  change (∑ j, S (D j m) ⊗ₜ[R]
      CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i (n + 1) (Tensor.KoszulTensor.exteriorWedge R σ j (n + 1) ω)) +
    Tensor.KoszulTensor.differential R σ M D n (S m ⊗ₜ[R] CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i n ω) +
      ((m - S (D i m)) ⊗ₜ[R] (ω - Tensor.KoszulTensor.exteriorWedge R σ i n (CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i n ω)) +
        (m - D i (S m)) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ i n (CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction R σ i n ω)) = _
  rw [Tensor.KoszulTensor.differential_tmul, ← Finset.sum_add_distrib, hsum]
  apply tensor_split
  simpa only [Finsupp.single_eq_same, one_smul] using CoordinateHomotopy.KoszulCoordinateHomotopy.contraction_wedge R σ i i n ω

variable (hcomm : ∀ j l, Function.Commute (D j) (D l))

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hcomm

include hcommS in
theorem projectionChain_f (n : ℕ) :
    (CoordinateHomotopy.KoszulCoordinateHomotopy.projectionChain R σ M D i S hcomm).f n =
      ModuleCat.ofHom (projection R σ M D i S n) := by
  have hb : (show Module.End R (Tensor.KoszulTensor.Term R σ M n) from
      ((CoordinateHomotopy.KoszulCoordinateHomotopy.boundary R σ M D i S hcomm).f n).hom) +
        projection R σ M D i S n = LinearMap.id := by
    cases n with
    | zero =>
      have hz := congrArg (fun f : (K).X 0 ⟶ (K).X 0 => f.hom)
        (CoordinateHomotopy.KoszulCoordinateHomotopy.boundary_zero R σ M D i S hcomm)
      exact (congrArg (fun f : Module.End R (Tensor.KoszulTensor.Term R σ M 0) => f + projection R σ M D i S 0)
        hz).trans (CoordinateHomotopy.KoszulCoordinateHomotopy.homotopy_zero_linear R σ M D i S)
    | succ n =>
      have hs := congrArg (fun f : (K).X (n + 1) ⟶ (K).X (n + 1) => f.hom)
        (CoordinateHomotopy.KoszulCoordinateHomotopy.boundary_succ R σ M D i S hcomm n)
      exact (congrArg (fun f : Module.End R (Tensor.KoszulTensor.Term R σ M (n + 1)) => f + projection R σ M D i S (n + 1))
        hs).trans (homotopy_succ R σ M D i S hcommS n)
  apply ModuleCat.hom_ext
  change LinearMap.id - (show Module.End R (Tensor.KoszulTensor.Term R σ M n) from
    ((CoordinateHomotopy.KoszulCoordinateHomotopy.boundary R σ M D i S hcomm).f n).hom) = projection R σ M D i S n
  exact sub_eq_iff_eq_add.mpr (hb.symm.trans (add_comm _ _))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.PartialPrimitive.KoszulPartialPrimitive
