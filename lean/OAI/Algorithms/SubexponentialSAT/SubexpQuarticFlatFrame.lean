import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatData

namespace OAI.Algorithms

/-! Store frames and fixed caller ports for the flat quartic service. -/

namespace SubexponentialSAT.SubexpQuarticFlatMul

open StackRoutines SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

/-- Relative to a valid input store, only the consumed operands and product
output change. This form supports an arbitrary surrounding caller frame. -/
theorem finalStore_updates {B : ℕ} (modulus width : List Bool)
    (t a b result : Quad (Word B)) :
    finalStore modulus width t result =
      Function.update
        (Function.update (Function.update (initialStore modulus width t a b) 70 []) 71 [])
        72 (flat result) := by
  funext j
  by_cases h70 : j = 70
  · subst j
    simp [initialStore, finalStore, bankStore]
  · by_cases h71 : j = 71
    · subst j
      simp [initialStore, finalStore, bankStore]
    · by_cases h72 : j = 72
      · subst j
        simp [initialStore, finalStore, bankStore]
      · simp [initialStore, finalStore, bankStore, h70, h71, h72]


end SubexponentialSAT.SubexpQuarticFlatMul

namespace SubexponentialSAT.SubexpQuarticFlatLift

open StackRoutines SubexpQuarticRing SubexpQuarticFlatMul

theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- The only three stacks changed at the end of the multiplication call. -/
def resultStacks {s : ℕ} (ports : Fin 77 ↪ Fin s) (result : List Bool)
    (stk : Stacks (Fin s)) : Stacks (Fin s) :=
  Function.update (Function.update (Function.update stk (ports 70) []) (ports 71) [])
    (ports 72) result

/-- Registers outside the assigned eight registers retain their caller values. -/
noncomputable def resultRegs {r : ℕ} (registers : Fin 8 ↪ Fin r)
    (values : Fin 8 → Bool) (regs : Fin r → Bool) : Fin r → Bool :=
  Function.extend registers values regs

theorem resultStacks_frame {s : ℕ} (ports : Fin 77 ↪ Fin s) (result : List Bool)
    (stk : Stacks (Fin s)) (j : Fin s)
    (h70 : j ≠ ports 70) (h71 : j ≠ ports 71) (h72 : j ≠ ports 72) :
    resultStacks ports result stk j = stk j := by
  simp [resultStacks, h70, h71, h72]

theorem resultRegs_frame {r : ℕ} (registers : Fin 8 ↪ Fin r)
    (values : Fin 8 → Bool) (regs : Fin r → Bool) (j : Fin r)
    (hj : ¬ ∃ i, registers i = j) : resultRegs registers values regs j = regs j :=
  Function.extend_apply' _ _ _ hj

theorem extend_final {s B : ℕ} (ports : Fin 77 ↪ Fin s)
    (modulus width : List Bool) (t a b result : Quad (Word B))
    (stk : Stacks (Fin s))
    (h : ∀ i, stk (ports i) = initialStore modulus width t a b i) :
    Function.extend ports (finalStore modulus width t result) stk =
      resultStacks ports (flat result) stk := by
  rw [finalStore_updates modulus width t a b result]
  simp only [ProgramLinking.extend_update ports.injective]
  rw [extend_agree ports _ stk h]
  rfl


/-- The dense-polynomial caller reserves registers 0--7 for this subroutine. -/
def denseRegisters : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective 8 8⟩

/-- The 61 bank words occupy 30--90; the modulus is the caller's stack 5.
Inputs/output occupy 11/12/13, with reduction cache 91 and unary width 10. -/
def densePort (i : Fin 77) : Fin 128 :=
  if h : i.val < 61 then ⟨i.val + 30, by omega⟩
  else ![0,1,2,3,4,5,6,7,8,11,12,13,91,10,14,15] ⟨i.val - 61, by omega⟩

def densePorts : Fin 77 ↪ Fin 128 := ⟨densePort, by decide⟩


end SubexponentialSAT.SubexpQuarticFlatLift

end OAI.Algorithms
