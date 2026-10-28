import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram

namespace OAI.Algorithms

/-!
# Retained storage for the actual layout construction

The first five words are the combined scopes, combined factor tables, packed
assignment, framed word alphabet, and word-width shape. The remaining slots
are reserved for the later concrete type, matrix, and basis producers.
All thirty-two words lie below the fixed ordinary-work cleanup boundary.
-/

namespace SubexponentialSAT.SubexpLayoutPorts

open SubexpMainProgram

structure Allocation (es : ℕ) where
  ordinaryCount : ℕ
  enough : 672 ≤ ordinaryCount
  within : ordinaryCount ≤ workStacks es

def ordinary {es : ℕ} (a : Allocation es) (i : Fin 672) : Fin (totalStacks es) :=
  ⟨i.val, by have := a.enough.trans a.within; dsimp [totalStacks]; omega⟩

def master {es : ℕ} (a : Allocation es) (i : Fin 32) : Fin (totalStacks es) :=
  ordinary a ⟨640 + i.val, by omega⟩

@[simp] theorem master_val {es : ℕ} (a : Allocation es) (i : Fin 32) :
    (master a i).val = 640 + i.val := rfl

theorem ordinary_injective {es : ℕ} (a : Allocation es) :
    Function.Injective (ordinary a) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (totalStacks es) => x.val) h)

theorem master_injective {es : ℕ} (a : Allocation es) :
    Function.Injective (master a) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
  simp only [master_val] at hv
  omega

theorem master_below_cleanup {es : ℕ} (a : Allocation es) (i : Fin 32) :
    (master a i).val < a.ordinaryCount := by
  have := a.enough
  simp only [master_val]
  omega

theorem master_ne_persistent {es : ℕ} (a : Allocation es) (i j : Fin 32) :
    master a i ≠ persistent es j := by
  intro h
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
  have hi := master_below_cleanup a i
  have := a.within
  simp only [persistent, Fin.val_natAdd] at hv
  omega

theorem master_ne_low {es : ℕ} (a : Allocation es) (i : Fin 32)
    (j : Fin (totalStacks es)) (hj : j.val < 640) : master a i ≠ j := by
  intro h
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
  simp only [master_val] at hv
  omega

def scopes {es : ℕ} (a : Allocation es) := master a 0
def tables {es : ℕ} (a : Allocation es) := master a 1
def assignment {es : ℕ} (a : Allocation es) := master a 2
def wordAlphabet {es : ℕ} (a : Allocation es) := master a 3
def wordWidth {es : ℕ} (a : Allocation es) := master a 4

end SubexponentialSAT.SubexpLayoutPorts

end OAI.Algorithms
