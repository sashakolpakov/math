import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed allocation of the local-basis batch inside Main. -/

namespace SubexponentialSAT.SubexpMainLocalBasisPorts

open BitProgram StructuredCalls SubexpMainProgram SubexpLayoutPorts

/-- Address 672 is the single persistent input, binary R. All other addresses
are ordinary workspace locations. -/
def highAddress : Fin 24 → Fin 673 :=
  ![650, 663, 661, 649, 111, 645, 646, 114, 647, 664,
    117, 118, 119, 120, 121, 122, 123, 124, 125, 126,
    654, 672, 318, 319]

def address : Fin 131 → Fin 673 :=
  Fin.addCases (m := 107) (n := 24) (motive := fun _ => Fin 673)
    (fun i => i.castLE (by decide))
    highAddress

theorem highAddress_injective : Function.Injective highAddress := by decide

theorem highAddress_large (i : Fin 24) : 107 ≤ (highAddress i).val := by
  fin_cases i <;> decide

theorem address_injective : Function.Injective address := by
  intro i
  refine Fin.addCases (m := 107) (n := 24)
    (motive := fun i ↦ ∀ j, address i = address j → i = j) ?_ ?_ i
  · intro a j
    refine Fin.addCases (m := 107) (n := 24)
      (motive := fun j ↦ address (a.castAdd 24) = address j → a.castAdd 24 = j)
      ?_ ?_ j
    · intro b h
      simp only [address, Fin.addCases_left] at h
      apply Fin.ext
      simpa only [Fin.val_castAdd, Fin.val_castLE] using congrArg Fin.val h
    · intro b h
      simp only [address, Fin.addCases_left, Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castLE] at hv
      have hl := highAddress_large b
      omega
  · intro a j
    refine Fin.addCases (m := 107) (n := 24)
      (motive := fun j ↦ address (a.natAdd 107) = address j → a.natAdd 107 = j)
      ?_ ?_ j
    · intro b h
      simp only [address, Fin.addCases_left, Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castLE] at hv
      have hl := highAddress_large a
      omega
    · intro b h
      simp only [address, Fin.addCases_right] at h
      exact congrArg (Fin.natAdd 107) (highAddress_injective h)

def location {es : ℕ} (alloc : Allocation es) (i : Fin 673) : Fin (totalStacks es) :=
  if h : i.val < 672 then ordinary alloc ⟨i.val, h⟩ else persistent es 25

theorem location_of_ordinary {es : ℕ} (alloc : Allocation es) (i : Fin 673)
    (hi : i.val < 672) : location alloc i = ordinary alloc ⟨i.val, hi⟩ := by
  simp only [location, dite_eq_left hi]

theorem location_of_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 673)
    (hi : ¬i.val < 672) : location alloc i = persistent es 25 := by
  simp only [location, dite_eq_right hi]

theorem location_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (location alloc) := by
  intro i j h
  have hw := alloc.enough.trans alloc.within
  by_cases hi : i.val < 672 <;> by_cases hj : j.val < 672
  · have hv := congrArg Fin.val ((location_of_ordinary alloc i hi).symm.trans
      (h.trans (location_of_ordinary alloc j hj)))
    apply Fin.ext
    simpa only [ordinary] using hv
  · have hv := congrArg Fin.val ((location_of_ordinary alloc i hi).symm.trans
      (h.trans (location_of_persistent alloc j hj)))
    simp only [ordinary, persistent, Fin.val_natAdd] at hv
    omega
  · have hv := congrArg Fin.val ((location_of_persistent alloc i hi).symm.trans
      (h.trans (location_of_ordinary alloc j hj)))
    simp only [ordinary, persistent, Fin.val_natAdd] at hv
    omega
  · apply Fin.ext
    omega

def stackMap {es : ℕ} (alloc : Allocation es) : Fin 131 → Fin (totalStacks es) :=
  location alloc ∘ address

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) :=
  (location_injective alloc).comp address_injective

def masterLocal : Fin 9 → Fin 131 := ![107, 108, 109, 110, 112, 113, 115, 116, 127]
def masterIndex : Fin 9 → Fin 32 := ![10, 23, 21, 9, 5, 6, 7, 24, 14]

@[simp] theorem stackMap_master {es : ℕ} (alloc : Allocation es) (i : Fin 9) :
    stackMap alloc (masterLocal i) = master alloc (masterIndex i) := by
  fin_cases i <;> rfl

@[simp] theorem stackMap_counter {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 128 = persistent es 25 := rfl
@[simp] theorem stackMap_length {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 111 = ordinary alloc 111 := rfl
@[simp] theorem stackMap_width {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 114 = ordinary alloc 114 := rfl
@[simp] theorem stackMap_copy {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 129 = ordinary alloc 318 := rfl
@[simp] theorem stackMap_temporary {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 130 = ordinary alloc 319 := rfl
@[simp] theorem stackMap_output {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 127 = master alloc 14 := rfl

theorem stackMap_low {es : ℕ} (alloc : Allocation es) (i : Fin 107) :
    stackMap alloc (i.castAdd 24) = ordinary alloc (i.castLE (by decide)) := by
  simp only [stackMap, Function.comp_apply, address, Fin.addCases_left]
  simp only [location, Fin.val_castLE, dite_eq_left (by omega : i.val < 672)]
  rfl

private theorem address_avoids_source (i : Fin 131) :
    (address i).val < 128 ∨ 318 ≤ (address i).val := by
  have h : ∀ j : Fin 131, (address j).val < 128 ∨ 318 ≤ (address j).val := by decide
  exact h i

/-- The source-ring caches are not among the batch or conversion ports. -/
theorem stackMap_avoids_source {es : ℕ} (alloc : Allocation es) (i : Fin 10) :
    ¬ ∃ j, stackMap alloc j = ordinary alloc ⟨128 + i.val, by omega⟩ := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  have hr := address_avoids_source j
  have hw := alloc.enough.trans alloc.within
  by_cases ha : (address j).val < 672
  · rw [show stackMap alloc j = location alloc (address j) from rfl,
      location_of_ordinary alloc (address j) ha] at hj
    have hv := congrArg Fin.val hj
    simp only [ordinary] at hv
    omega
  · rw [show stackMap alloc j = location alloc (address j) from rfl,
      location_of_persistent alloc (address j) ha] at hj
    have hv := congrArg Fin.val hj
    simp only [ordinary, persistent, Fin.val_natAdd] at hv
    omega

theorem stackMap_avoids_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 32)
    (hi : i ≠ 25) : ¬ ∃ j, stackMap alloc j = persistent es i := by
  rintro ⟨j, hj⟩
  have hw := alloc.enough.trans alloc.within
  by_cases ha : (address j).val < 672
  · rw [show stackMap alloc j = location alloc (address j) from rfl,
      location_of_ordinary alloc (address j) ha] at hj
    have hv := congrArg Fin.val hj
    simp only [ordinary, persistent, Fin.val_natAdd] at hv
    omega
  · apply hi
    apply (persistent_injective es)
    symm
    rw [show stackMap alloc j = location alloc (address j) from rfl,
      location_of_persistent alloc (address j) ha] at hj
    exact hj

def registers (er : ℕ) (hr : 16 ≤ er) : Fin 32 ↪ Fin (workRegs er) :=
  ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩

def registerMap (er : ℕ) (hr : 16 ≤ er) : Fin 32 → Fin (totalRegs er) :=
  workRegister er ∘ registers er hr

theorem registerMap_injective (er : ℕ) (hr : 16 ≤ er) :
    Function.Injective (registerMap er hr) :=
  (workRegister_injective er).comp (registers er hr).injective

end SubexponentialSAT.SubexpMainLocalBasisPorts

end OAI.Algorithms
