import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PowerModuleSequence
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.Pi

/-! # Adic Modules -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicModules

noncomputable section

/-! Principal-adic completeness of products and separation detected by nilpotent coordinates. -/

universe u v w

variable (R : Type u) [CommRing R] (r : R)
  {ι : Type w} (M : ι → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

theorem pi_mem (n : ℕ) (x : ∀ j, M j) :
    x ∈ (Ideal.span {r}) ^ n • (⊤ : Submodule R (∀ j, M j)) ↔
      ∀ j, x j ∈ (Ideal.span {r}) ^ n • (⊤ : Submodule R (M j)) := by
  simp only [PowerModuleSequence.mem_submodule]
  constructor
  · rintro ⟨y, rfl⟩ j
    exact ⟨y j, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

theorem pi_precomplete [∀ j, IsPrecomplete (Ideal.span {r}) (M j)] :
    IsPrecomplete (Ideal.span {r}) (∀ j, M j) := by
  constructor
  intro f hf
  have hcoord (j : ι) : ∃ L : M j, ∀ n,
      f n j ≡ L [SMOD ((Ideal.span {r}) ^ n • (⊤ : Submodule R (M j)))] := by
    apply IsPrecomplete.prec'
    intro m n hmn
    exact SModEq.sub_mem.mpr ((pi_mem R r M m (f m - f n)).mp
      (SModEq.sub_mem.mp (hf hmn)) j)
  choose L hL using hcoord
  refine ⟨L, fun n => SModEq.sub_mem.mpr ?_⟩
  exact (pi_mem R r M n (f n - L)).mpr (fun j => SModEq.sub_mem.mp (hL j n))

variable (A : ℕ → Type v) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  (S : Submodule R (∀ n, A n)) (hzero : ∀ n (x : A n), r ^ (n + 1) • x = 0)

include hzero in
theorem hausdorff : IsHausdorff (Ideal.span {r}) S := by
  constructor
  intro x hx
  apply Subtype.ext
  funext n
  obtain ⟨y, hy⟩ := (PowerModuleSequence.mem_submodule R S r (n + 1) x).mp
    (SModEq.zero.mp (hx (n + 1)))
  exact (congrArg (fun z : S => z.val n) hy).symm.trans (hzero n (y.val n))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicModules
