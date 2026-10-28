import Mathlib

/-! # Dual Pair -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.UnitarySplitting.DualPair.Construction

/-! Concrete matrix unitary groups and the trace tensor pairing for UnitarySplitting.
The involution is supplied as the nonidentity F-automorphism of E.
No splitting or representation is part of these definitions. -/

open scoped BigOperators Kronecker TensorProduct
open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def adjointMatrix (σ : E ≃ₐ[F] E) (A : Matrix I I E) : Matrix I I E :=
  (A.map σ).transpose

omit [Fintype I] in
@[simp] theorem adjointMatrix_one (σ : E ≃ₐ[F] E) :
    adjointMatrix σ (1 : Matrix I I E) = 1 := by
  ext i j
  simp [adjointMatrix, Matrix.one_apply, eq_comm]

omit [DecidableEq I] in
theorem adjointMatrix_mul (σ : E ≃ₐ[F] E) (A B : Matrix I I E) :
    adjointMatrix σ (A * B) = adjointMatrix σ B * adjointMatrix σ A := by
  ext i j
  simp [adjointMatrix, Matrix.mul_apply, mul_comm]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem adjointMatrix_kronecker (σ : E ≃ₐ[F] E)
    (A : Matrix I I E) (B : Matrix J J E) :
    adjointMatrix σ (A ⊗ₖ B) = adjointMatrix σ A ⊗ₖ adjointMatrix σ B := by
  ext i j
  simp [adjointMatrix]

/-- The full unitary group of H; valid for Hermitian and skew-Hermitian H. -/
def unitaryGroup (σ : E ≃ₐ[F] E) (H : Matrix I I E) :
    Subgroup (Matrix I I E)ˣ where
  carrier := {g | adjointMatrix σ (g : Matrix I I E) * H * (g : Matrix I I E) = H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change adjointMatrix σ ((a : Matrix I I E) * (b : Matrix I I E)) * H *
      ((a : Matrix I I E) * (b : Matrix I I E)) = H
    rw [adjointMatrix_mul]
    calc
      _ = adjointMatrix σ (b : Matrix I I E) *
          (adjointMatrix σ (a : Matrix I I E) * H * (a : Matrix I I E)) *
          (b : Matrix I I E) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [ha]; exact hb
  inv_mem' := by
    intro a ha
    have hadj : adjointMatrix σ (↑a⁻¹ : Matrix I I E) *
        adjointMatrix σ (a : Matrix I I E) = 1 := by
      rw [← adjointMatrix_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        adjointMatrix_one]
    calc
      adjointMatrix σ (↑a⁻¹ : Matrix I I E) * H * (↑a⁻¹ : Matrix I I E) =
          adjointMatrix σ (↑a⁻¹ : Matrix I I E) *
          (adjointMatrix σ (a : Matrix I I E) * H * (a : Matrix I I E)) *
          (↑a⁻¹ : Matrix I I E) := by rw [ha]
      _ = H := by
        simp only [← Matrix.mul_assoc, hadj, Matrix.one_mul]
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]

/-- Tensor product in the standard bases of E^I and E^J. -/
def tensorUnits (a : (Matrix I I E)ˣ) (b : (Matrix J J E)ˣ) :
    (Matrix (I × J) (I × J) E)ˣ where
  val := (a : Matrix I I E) ⊗ₖ (b : Matrix J J E)
  inv := (↑a⁻¹ : Matrix I I E) ⊗ₖ (↑b⁻¹ : Matrix J J E)
  val_inv := by rw [← Matrix.mul_kronecker_mul]; simp
  inv_val := by rw [← Matrix.mul_kronecker_mul]; simp

/-- The tensor action is a group homomorphism into the unitary group
of the tensor form, rather than an arbitrary supplied action. -/
def tensorUnitaryAction (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E) :
    (unitaryGroup σ H × unitaryGroup σ K) →* unitaryGroup σ (H ⊗ₖ K) where
  toFun g := ⟨tensorUnits g.1.val g.2.val, by
    change adjointMatrix σ (_ ⊗ₖ _) * (H ⊗ₖ K) * (_ ⊗ₖ _) = H ⊗ₖ K
    rw [adjointMatrix_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, g.1.property, g.2.property]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact Matrix.one_kronecker_one
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact Matrix.mul_kronecker_mul _ _ _ _

/-- Sesquilinear form, conjugate-linear in the first variable. -/
def sesquilinear (σ : E ≃ₐ[F] E) (H : Matrix I I E) (x y : I → E) : E :=
  dotProduct (fun i => σ (x i)) (H.mulVec y)

omit [DecidableEq I] in
theorem conjugate_mulVec (σ : E ≃ₐ[F] E) (A : Matrix I I E) (x : I → E) :
    (fun i => σ (A.mulVec x i)) = (A.map σ).mulVec (fun i => σ (x i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

omit [DecidableEq I] in
theorem sesquilinear_change (σ : E ≃ₐ[F] E) (H A : Matrix I I E)
    (x y : I → E) :
    sesquilinear σ H (A.mulVec x) (A.mulVec y) =
      sesquilinear σ (adjointMatrix σ A * H * A) x y := by
  unfold sesquilinear
  rw [conjugate_mulVec]
  simp only [adjointMatrix, Matrix.mulVec_mulVec, dotProduct_mulVec]
  rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem unitary_preserves (σ : E ≃ₐ[F] E) (H : Matrix I I E)
    (g : unitaryGroup σ H) (x y : I → E) :
    sesquilinear σ H ((g.val : Matrix I I E).mulVec x)
      ((g.val : Matrix I I E).mulVec y) = sesquilinear σ H x y := by
  rw [sesquilinear_change, g.property]

/-- The underlying F-valued trace pairing on V ⊗_E W in tensor coordinates. -/
def traceTensorPairing (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E)
    (x y : I × J → E) : F :=
  (Algebra.trace F E (sesquilinear σ (H ⊗ₖ K) x y)) / 2

theorem tensor_action_preserves_trace (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E)
    (g : unitaryGroup σ H × unitaryGroup σ K) (x y : I × J → E) :
    traceTensorPairing σ H K
      (((tensorUnitaryAction σ H K g).val : Matrix (I × J) (I × J) E).mulVec x)
      (((tensorUnitaryAction σ H K g).val : Matrix (I × J) (I × J) E).mulVec y) =
      traceTensorPairing σ H K x y := by
  unfold traceTensorPairing
  rw [unitary_preserves]

section Isometries

variable {R P : Type} [Field R] [AddCommGroup P] [Module R P]

/-- The actual F-linear isometry group of a specified pairing. -/
def pairingIsometries (β : P → P → R) : Subgroup (P ≃ₗ[R] P) where
  carrier := {g | ∀ x y, β (g x) (g y) = β x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g.symm x) (g.symm y)
    simpa using h.symm

/-- Pointwise convergence of an automorphism and its inverse. In finite
dimension this is the usual topology on the linear isometry group. -/
instance pairingIsometriesTopology [TopologicalSpace P] (β : P → P → R) :
    TopologicalSpace (pairingIsometries β) :=
  TopologicalSpace.induced
    (fun g : pairingIsometries β => ((fun x => g.val x), (fun x => g.val.symm x)))
    inferInstance

end Isometries

def matrixLinearEquiv (A : (Matrix I I E)ˣ) : (I → E) ≃ₗ[F] (I → E) :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.restrictScalars F

@[simp] theorem matrixLinearEquiv_apply (A : (Matrix I I E)ˣ) (x : I → E) :
    matrixLinearEquiv (F := F) A x = (A : Matrix I I E).mulVec x := rfl

@[simp] theorem matrixLinearEquiv_one :
    matrixLinearEquiv (F := F) (1 : (Matrix I I E)ˣ) = 1 := by
  ext x i
  simp

theorem matrixLinearEquiv_mul (A B : (Matrix I I E)ˣ) :
    matrixLinearEquiv (F := F) (A * B) =
      matrixLinearEquiv (F := F) A * matrixLinearEquiv (F := F) B := by
  ext x i
  exact congrFun (Matrix.mulVec_mulVec x (A : Matrix I I E) (B : Matrix I I E)).symm i

/-- The concrete symplectic action on the trace tensor space. -/
def dualPairAction (σ : E ≃ₐ[F] E) (H : Matrix I I E) (K : Matrix J J E) :
    (unitaryGroup σ H × unitaryGroup σ K) →*
      pairingIsometries (traceTensorPairing σ H K) where
  toFun g := ⟨matrixLinearEquiv (tensorUnitaryAction σ H K g).val,
    tensor_action_preserves_trace σ H K g⟩
  map_one' := by
    apply Subtype.ext
    change matrixLinearEquiv (tensorUnitaryAction σ H K 1).val = 1
    rw [map_one]
    exact matrixLinearEquiv_one
  map_mul' g h := by
    apply Subtype.ext
    change matrixLinearEquiv (tensorUnitaryAction σ H K (g * h)).val = _
    rw [map_mul]
    exact matrixLinearEquiv_mul _ _

section Topology

variable [TopologicalSpace E] [IsTopologicalRing E]

theorem dualPairAction_apply_continuous (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E) (x : I × J → E) :
    Continuous (fun g : unitaryGroup σ H × unitaryGroup σ K =>
      (dualPairAction σ H K g).val x) := by
  apply continuous_pi
  intro i
  change Continuous (fun g : unitaryGroup σ H × unitaryGroup σ K =>
    ∑ j, ((g.1.val : Matrix I I E) i.1 j.1 *
      (g.2.val : Matrix J J E) i.2 j.2) * x j)
  fun_prop

theorem dualPairAction_continuous (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E) :
    Continuous (dualPairAction σ H K) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_pi fun x => dualPairAction_apply_continuous σ H K x
  · apply continuous_pi
    intro x
    have h := (dualPairAction_apply_continuous σ H K x).comp
      (continuous_inv : Continuous (fun g : unitaryGroup σ H × unitaryGroup σ K => g⁻¹))
    simpa only [Function.comp_def, map_inv, Subgroup.coe_inv, LinearEquiv.coe_inv] using h

def continuousDualPairAction (σ : E ≃ₐ[F] E)
    (H : Matrix I I E) (K : Matrix J J E) :
    (unitaryGroup σ H × unitaryGroup σ K) →ₜ*
      pairingIsometries (traceTensorPairing σ H K) :=
  ⟨dualPairAction σ H K, dualPairAction_continuous σ H K⟩

end Topology

/-- The tensor-coordinate space used above is identified with the native
Lean tensor product by the tensor product of the two standard bases. -/
def tensorCoordinates : ((I → E) ⊗[E] (J → E)) ≃ₗ[E] (I × J → E) :=
  ((Pi.basisFun E I).tensorProduct (Pi.basisFun E J)).equivFun

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem tensorCoordinates_tmul (x : I → E) (y : J → E) (i : I × J) :
    tensorCoordinates (x ⊗ₜ[E] y) i = x i.1 * y i.2 := by
  rcases i with ⟨i, j⟩
  simp [tensorCoordinates, Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]

theorem tensorUnits_on_pure_tensors (a : (Matrix I I E)ˣ) (b : (Matrix J J E)ˣ)
    (x : I → E) (y : J → E) :
    (tensorUnits a b : Matrix (I × J) (I × J) E).mulVec
        (tensorCoordinates (x ⊗ₜ[E] y)) =
      tensorCoordinates (((a : Matrix I I E).mulVec x) ⊗ₜ[E]
        ((b : Matrix J J E).mulVec y)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, tensorCoordinates_tmul]
  change (∑ j : I × J, ((a : Matrix I I E) i.1 j.1 *
    (b : Matrix J J E) i.2 j.2) * (x j.1 * y j.2)) =
      (∑ j : I, (a : Matrix I I E) i.1 j * x j) *
      (∑ k : J, (b : Matrix J J E) i.2 k * y k)
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end RepresentationTheory.Weil.UnitarySplitting.DualPair.Construction

namespace RepresentationTheory.Weil.UnitarySplitting.DualPair.Transvections

/-! Symplectic transvections and their conjugation law. These are the
elementary transformations used in the surjectivity argument. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair.Construction

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)

def transvectionMap (v : V) (a : F) : V →ₗ[F] V :=
  LinearMap.id + a • (LinearMap.toSpanSingleton F V v).comp (B v)

theorem transvectionMap_apply (v x : V) (a : F) :
    transvectionMap B v a x = x + (a * B v x) • v := by
  simp only [transvectionMap, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, smul_smul]

include hAlt in
theorem transvectionMap_inverse (v x : V) (a : F) :
    transvectionMap B v (-a) (transvectionMap B v a x) = x := by
  rw [transvectionMap_apply, transvectionMap_apply]
  simp only [map_add, map_smul, hAlt.self_eq_zero v, neg_mul, neg_smul]
  module

def transvectionEquiv (v : V) (a : F) : V ≃ₗ[F] V where
  toLinearMap := transvectionMap B v a
  invFun := transvectionMap B v (-a)
  left_inv x := transvectionMap_inverse B hAlt v x a
  right_inv x := by
    change transvectionMap B v a (transvectionMap B v (-a) x) = x
    simpa only [neg_neg] using transvectionMap_inverse B hAlt v x (-a)

theorem transvection_preserves (v x y : V) (a : F) :
    B (transvectionEquiv B hAlt v a x) (transvectionEquiv B hAlt v a y) = B x y := by
  change B (transvectionMap B v a x) (transvectionMap B v a y) = B x y
  rw [transvectionMap_apply, transvectionMap_apply]
  have hvx : B x v = -B v x := by rw [← hAlt.neg_eq v x]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hAlt.self_eq_zero v, hvx]
  ring

def transvection (v : V) (a : F) : Construction.pairingIsometries (fun x y => B x y) :=
  ⟨transvectionEquiv B hAlt v a, fun x y => transvection_preserves B hAlt v x y a⟩

theorem transvection_apply (v x : V) (a : F) :
    (transvection B hAlt v a).val x = x + (a * B v x) • v :=
  transvectionMap_apply B v x a

theorem transvection_fix_of_pairing_zero (v x : V) (a : F) (hx : B v x = 0) :
    (transvection B hAlt v a).val x = x := by
  rw [transvection_apply, hx, mul_zero, zero_smul, add_zero]

theorem transvection_conjugation
    (g : Construction.pairingIsometries (fun x y => B x y)) (v : V) (a : F) :
    g * transvection B hAlt v a * g⁻¹ = transvection B hAlt (g.val v) a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val ((transvection B hAlt v a).val (g.val.symm x)) =
    (transvection B hAlt (g.val v) a).val x
  rw [transvection_apply, map_add, map_smul, g.val.apply_symm_apply, transvection_apply]
  have hp : B (g.val v) x = B v (g.val.symm x) := by
    have hh := g.property v (g.val.symm x)
    simpa only [g.val.apply_symm_apply] using hh
  rw [hp]

theorem transvection_sends_of_pairing_ne_zero (u w : V) (huw : B w u ≠ 0) :
    (transvection B hAlt (w - u) (B w u)⁻¹).val u = w := by
  rw [transvection_apply]
  have hp : B (w - u) u = B w u := by
    simp only [map_sub, LinearMap.sub_apply, hAlt.self_eq_zero u, sub_zero]
  rw [hp, inv_mul_cancel₀ huw, one_smul]
  module

def transvectionSubgroup : Subgroup (Construction.pairingIsometries (fun x y => B x y)) :=
  Subgroup.closure (Set.range (fun p : V × F => transvection B hAlt p.1 p.2))

theorem transvection_mem (v : V) (a : F) :
    transvection B hAlt v a ∈ transvectionSubgroup B hAlt :=
  Subgroup.subset_closure ⟨(v, a), rfl⟩

theorem exists_common_pairing (hND : B.Nondegenerate) (u w : V) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ z : V, B u z ≠ 0 ∧ B w z ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, B u y ≠ 0 := by
    by_contra! h
    exact hu (hND.1 u h)
  obtain ⟨z, hz⟩ : ∃ z, B w z ≠ 0 := by
    by_contra! h
    exact hw (hND.1 w h)
  by_cases hwy : B w y = 0
  · by_cases huz : B u z = 0
    · refine ⟨y + z, ?_, ?_⟩
      · simpa only [map_add, huz, add_zero] using hy
      · simpa only [map_add, hwy, zero_add] using hz
    · exact ⟨z, huz, hz⟩
  · exact ⟨y, hy, hwy⟩

theorem exists_transvection_word_sends (hND : B.Nondegenerate)
    (u w : V) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ g ∈ transvectionSubgroup B hAlt, g.val u = w := by
  obtain ⟨z, huz, hwz⟩ := exists_common_pairing B hND u w hu hw
  have hzu : B z u ≠ 0 := by
    rw [← hAlt.neg_eq u z]
    exact neg_ne_zero.mpr huz
  let t₁ := transvection B hAlt (z - u) (B z u)⁻¹
  let t₂ := transvection B hAlt (w - z) (B w z)⁻¹
  refine ⟨t₂ * t₁, (transvectionSubgroup B hAlt).mul_mem (transvection_mem B hAlt _ _)
    (transvection_mem B hAlt _ _), ?_⟩
  change t₂.val (t₁.val u) = w
  rw [transvection_sends_of_pairing_ne_zero B hAlt u z hzu]
  exact transvection_sends_of_pairing_ne_zero B hAlt z w hwz

theorem exists_transvection_word_fixes_sends [CharZero F]
    (u v w : V) (huv : B u v = 1) (huw : B u w = 1) :
    ∃ g ∈ transvectionSubgroup B hAlt, g.val u = u ∧ g.val v = w := by
  classical
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset ({0, B w v} : Finset F)
  have hboth : k ≠ 0 ∧ k ≠ B w v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk
  have hk0 := hboth.1
  have hkw := hboth.2
  let z := v + k • u
  have hvu : B v u = -1 := by rw [← hAlt.neg_eq u v, huv]
  have hwu : B w u = -1 := by rw [← hAlt.neg_eq u w, huw]
  have hzv : B z v ≠ 0 := by
    simpa [z, hAlt.self_eq_zero v, huv] using hk0
  have hwz : B w z ≠ 0 := by
    simpa only [z, map_add, map_smul, hwu, smul_eq_mul, mul_neg, mul_one,
      ← sub_eq_add_neg] using sub_ne_zero.mpr hkw.symm
  have h₁u : B (z - v) u = 0 := by
    simp [z, hAlt.self_eq_zero u]
  have h₂u : B (w - z) u = 0 := by
    simp [z, hvu, hwu, hAlt.self_eq_zero u]
  let t₁ := transvection B hAlt (z - v) (B z v)⁻¹
  let t₂ := transvection B hAlt (w - z) (B w z)⁻¹
  refine ⟨t₂ * t₁, (transvectionSubgroup B hAlt).mul_mem (transvection_mem B hAlt _ _)
    (transvection_mem B hAlt _ _), ?_, ?_⟩
  · change t₂.val (t₁.val u) = u
    rw [transvection_fix_of_pairing_zero B hAlt (z - v) u _ h₁u]
    exact transvection_fix_of_pairing_zero B hAlt (w - z) u _ h₂u
  · change t₂.val (t₁.val v) = w
    rw [transvection_sends_of_pairing_ne_zero B hAlt v z hzv]
    exact transvection_sends_of_pairing_ne_zero B hAlt z w hwz

end RepresentationTheory.Weil.UnitarySplitting.DualPair.Transvections

end

end OAI
