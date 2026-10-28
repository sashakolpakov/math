import OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference

/-! # Adic Compatible -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCompatible.AdicCompatibleSequences

noncomputable section

/-! All-transition compatibility agrees with successive compatibility, and
discarding the first level preserves the actual inverse sequence module. -/

variable (R : Type*) [CommRing R] (B : ℕ → Type*)
  [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
  (t : ∀ n m : ℕ, n ≤ m → B m →ₗ[R] B n)
  (hid : ∀ n x, t n n le_rfl x = x)
  (hcomp : ∀ n m l (hnm : n ≤ m) (hml : m ≤ l) x,
    t n m hnm (t m l hml x) = t n l (hnm.trans hml) x)

include hid hcomp in
theorem compatible_iff_successor (x : ∀ n, B n) :
    x ∈ AdicCohomology.AdicCohomologyLimit.compatible B t ↔
      ∀ n, t n (n + 1) (Nat.le_succ n) (x (n + 1)) = x n := by
  refine ⟨fun h n => h n (n + 1) (Nat.le_succ n), ?_⟩
  intro h n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact hid n (x n)
  | succ m hnm ih =>
    exact (hcomp n m (m + 1) hnm (Nat.le_succ m) (x (m + 1))).symm.trans
      ((congrArg (t n m hnm) (h m)).trans ih)

def sequentialEquiv : AdicCohomology.AdicCohomologyLimit.compatible B t ≃ₗ[R]
    LinearMap.ker (IntegralComparison.SequentialModuleDifference.difference R B
      (fun n => t n (n + 1) (Nat.le_succ n))) where
  toFun x := ⟨x.val, (IntegralComparison.SequentialModuleDifference.difference_eq_zero_iff R B _ x.val).mpr
    ((compatible_iff_successor R B t hid hcomp x.val).mp x.property)⟩
  invFun x := ⟨x.val, (compatible_iff_successor R B t hid hcomp x.val).mpr
    ((IntegralComparison.SequentialModuleDifference.difference_eq_zero_iff R B _ x.val).mp x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shiftMap : AdicCohomology.AdicCohomologyLimit.compatible B t →ₗ[R]
    AdicCohomology.AdicCohomologyLimit.compatible (fun n => B (n + 1))
      (fun n m h => t (n + 1) (m + 1) (Nat.add_le_add_right h 1)) where
  toFun x := ⟨fun n => x.val (n + 1), fun n m h => x.property (n + 1) (m + 1) (Nat.add_le_add_right h 1)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def prepend (x : AdicCohomology.AdicCohomologyLimit.compatible (fun n => B (n + 1))
    (fun n m h => t (n + 1) (m + 1) (Nat.add_le_add_right h 1))) : ∀ n, B n
  | 0 => t 0 1 (by omega) (x.val 0)
  | n + 1 => x.val n

include hid hcomp in
theorem prepend_compatible (x : AdicCohomology.AdicCohomologyLimit.compatible (fun n => B (n + 1))
    (fun n m h => t (n + 1) (m + 1) (Nat.add_le_add_right h 1))) :
    prepend R B t x ∈ AdicCohomology.AdicCohomologyLimit.compatible B t := by
  intro n m h
  cases n with
  | zero =>
    cases m with
    | zero => exact hid 0 _
    | succ m =>
      change t 0 (m + 1) h (x.val m) = t 0 1 (by omega) (x.val 0)
      exact (hcomp 0 1 (m + 1) (by omega) (by omega) (x.val m)).symm.trans
        (congrArg (t 0 1 (by omega)) (x.property 0 m (Nat.zero_le m)))
  | succ n =>
    cases m with
    | zero => omega
    | succ m => exact x.property n m (Nat.le_of_succ_le_succ h)

include hid hcomp in
theorem shiftMap_bijective : Function.Bijective (shiftMap R B t) := by
  constructor
  · intro x y h
    have he : ∀ n, x.val (n + 1) = y.val (n + 1) :=
      fun n => congrArg (fun z => z.val n) h
    apply Subtype.ext
    funext n
    cases n with
    | zero =>
      exact (x.property 0 1 (by omega)).symm.trans
        ((congrArg (t 0 1 (by omega)) (he 0)).trans (y.property 0 1 (by omega)))
    | succ n => exact he n
  · intro x
    exact ⟨⟨prepend R B t x, prepend_compatible R B t hid hcomp x⟩, rfl⟩

def shiftEquiv : AdicCohomology.AdicCohomologyLimit.compatible B t ≃ₗ[R]
    AdicCohomology.AdicCohomologyLimit.compatible (fun n => B (n + 1))
      (fun n m h => t (n + 1) (m + 1) (Nat.add_le_add_right h 1)) :=
  LinearEquiv.ofBijective (shiftMap R B t) (shiftMap_bijective R B t hid hcomp)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCompatible.AdicCompatibleSequences
