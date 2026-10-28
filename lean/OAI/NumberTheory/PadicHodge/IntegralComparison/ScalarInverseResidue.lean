import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CompatibleLifting
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicModules
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Scalar Inverse Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarInverseResidue

noncomputable section

/-! The kernel of reduction on a finite scalar-exact inverse system is precisely the scalar multiple of its limit. -/

universe u v

variable (R : Type u) [CommRing R] (r : R) (M : ℕ → Type v)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n)

def compatible : Submodule R (∀ n, M n) :=
  LinearMap.ker (SequentialModuleDifference.difference R M t)

def evaluation : compatible R M t →ₗ[R] M 0 :=
  (LinearMap.proj 0).comp (compatible R M t).subtype

variable (j : ∀ n, M n →ₗ[R] M (n + 1)) (q : ∀ n, M n →ₗ[R] M 0)
  (hj : ∀ n x, j n (t n x) = r • x)
  (ht : ∀ n x, t n (j n x) = r • x)
  (hqzero : q 0 = LinearMap.id) (hq : ∀ n x, q (n + 1) x = q n (t n x))
  (hexact : ∀ n x, q (n + 1) x = 0 ↔ ∃ y, j n y = x)

include hqzero hq in
theorem projection (x : compatible R M t) (n : ℕ) : q n (x.val n) = x.val 0 := by
  have hx := (SequentialModuleDifference.difference_eq_zero_iff R M t x.val).mp x.property
  induction n with
  | zero => rw [hqzero]; rfl
  | succ n ih => rw [hq, hx, ih]

include hj ht hqzero hq hexact in
theorem divisible [∀ n, Finite (M n)] (x : compatible R M t) (hx : evaluation R M t x = 0) :
    ∃ y : compatible R M t, r • y = x := by
  have hx' := (SequentialModuleDifference.difference_eq_zero_iff R M t x.val).mp x.property
  have hn (n : ℕ) : ∃ y, j n y = x.val (n + 1) :=
    (hexact n _).mp ((projection R M t q hqzero hq x (n + 1)).trans hx)
  obtain ⟨y, hy, hxy⟩ := IntegralComparison.Finite.CompatibleLifting.exists_lift R M (fun n => M (n + 1)) t
    (fun n => t (n + 1)) j (fun n a => (hj n a).trans (ht (n + 1) a).symm)
    (fun n => x.val (n + 1)) (fun n => hx' (n + 1)) hn
  refine ⟨⟨y, (SequentialModuleDifference.difference_eq_zero_iff R M t y).mpr hy⟩, ?_⟩
  apply Subtype.ext
  funext n
  exact (ht n (y n)).symm.trans ((congrArg (t n) (hxy n)).trans (hx' n))

variable (hrzero : ∀ x : M 0, r • x = 0)

include hj ht hqzero hq hexact hrzero in
theorem kernel [∀ n, Finite (M n)] : LinearMap.ker (evaluation R M t) =
    (Ideal.span {r}) • (⊤ : Submodule R (compatible R M t)) := by
  ext x
  rw [LinearMap.mem_ker]
  have hmem : x ∈ (Ideal.span {r}) • (⊤ : Submodule R (compatible R M t)) ↔
      ∃ y : compatible R M t, r • y = x := by
    simpa only [Principal.PowerModuleSequence.submodule, pow_one] using
      Principal.PowerModuleSequence.mem_submodule R (compatible R M t) r 1 x
  rw [hmem]
  constructor
  · exact divisible R r M t j q hj ht hqzero hq hexact x
  · rintro ⟨y, rfl⟩
    exact (evaluation R M t).map_smul r y |>.trans (hrzero (evaluation R M t y))

include hj ht hqzero hq hexact hrzero in
theorem finite_residue [∀ n, Finite (M n)] :
    Finite (compatible R M t ⧸ ((Ideal.span {r}) • (⊤ : Submodule R (compatible R M t)))) := by
  rw [← kernel R r M t j q hj ht hqzero hq hexact hrzero]
  exact Finite.of_injective (evaluation R M t).quotKerEquivRange
    (evaluation R M t).quotKerEquivRange.injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarInverseResidue
