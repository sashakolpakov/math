import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts

namespace OAI.Algorithms

/-! Fixed placement of the coefficient adapter's local work bank in Main. -/

namespace SubexponentialSAT.SubexpMainCoefficients

open SubexpMainProgram SubexpLayoutPorts

def low {es : ℕ} (a : Allocation es) (i : Fin 64) : Fin (totalStacks es) :=
  ordinary a (i.castLE (by decide))

def stackMap {es : ℕ} (a : Allocation es) (i : Fin 64) : Fin (totalStacks es) :=
  if i = 40 then persistent es 6 else
  if i = 41 then persistent es 21 else
  if i = 42 then persistent es 17 else
  if i = 43 then persistent es 25 else
  if i = 48 then master a 9 else
  if i = 49 then ordinary a 254 else low a i

theorem stackMap_val {es : ℕ} (a : Allocation es) (i : Fin 64) :
    (stackMap a i).val =
      if i = 40 then workStacks es + 6 else
      if i = 41 then workStacks es + 21 else
      if i = 42 then workStacks es + 17 else
      if i = 43 then workStacks es + 25 else
      if i = 48 then 649 else if i = 49 then 254 else i.val := by
  unfold stackMap
  split_ifs <;> rfl

theorem stackMap_injective {es : ℕ} (a : Allocation es) : Function.Injective (stackMap a) := by
  intro i j h
  have hw := a.enough.trans a.within
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) h
  change (stackMap a i).val = (stackMap a j).val at hv
  rw [stackMap_val, stackMap_val] at hv
  clear h
  apply Fin.ext
  split_ifs at hv <;> omega

end SubexponentialSAT.SubexpMainCoefficients

end OAI.Algorithms
