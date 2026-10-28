import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts

namespace OAI.Algorithms

/-!
# Main allocation for the widened node traversal

The 288-stack worker retains its native 256-stack work area and reads the
32 layout masters through its added ports. The outer traversal moves its
old 64-stack bookkeeping area to local288..351. The Main allocation restores
those bookkeeping ports to ordinary256..319 and keeps the CRT bank disjoint.
-/

namespace SubexponentialSAT.SubexpMainMomentPorts

open SubexpMainProgram SubexpLayoutPorts

attribute [local simp] Fin.coe_ofNat_eq_mod

def baseMap {es : ℕ} (alloc : Allocation es) (i : Fin 352) : Fin (totalStacks es) :=
  if hlo : i.val < 256 then ordinary alloc ⟨i.val, by omega⟩
  else if hstatic : i.val < 288 then master alloc ⟨i.val - 256, by omega⟩
  else ordinary alloc ⟨i.val - 32, by omega⟩

theorem baseMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (baseMap alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  by_cases hi : i.val < 256 <;> by_cases hj : j.val < 256
  · simpa only [baseMap, dite_eq_left hi, dite_eq_left hj, ordinary] using hv
  · by_cases hj' : j.val < 288
    · simp only [baseMap, dite_eq_left hi, dite_eq_right hj, dite_eq_left hj', ordinary, master_val] at hv
      omega
    · simp only [baseMap, dite_eq_left hi, dite_eq_right hj, dite_eq_right hj', ordinary] at hv
      omega
  · by_cases hi' : i.val < 288
    · simp only [baseMap, dite_eq_right hi, dite_eq_left hi', dite_eq_left hj, ordinary, master_val] at hv
      omega
    · simp only [baseMap, dite_eq_right hi, dite_eq_right hi', dite_eq_left hj, ordinary] at hv
      omega
  · by_cases hi' : i.val < 288 <;> by_cases hj' : j.val < 288
    all_goals (simp [baseMap, hi, hj, hi', hj', ordinary, master] at hv; omega)

theorem baseMap_below {es : ℕ} (alloc : Allocation es) (i : Fin 352) :
    (baseMap alloc i).val < 672 := by
  by_cases hi : i.val < 256
  · simpa only [baseMap, dite_eq_left hi, ordinary] using (show i.val < 672 by omega)
  · by_cases hj : i.val < 288
    · simp only [baseMap, dite_eq_right hi, dite_eq_left hj, master_val]
      omega
    · simp only [baseMap, dite_eq_right hi, dite_eq_right hj, ordinary]
      omega

theorem baseMap_ne_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 352) (j : Fin 32) :
    baseMap alloc i ≠ persistent es j := by
  intro h
  have hv := congrArg Fin.val h
  have hlow := baseMap_below alloc i
  have hwork := alloc.enough.trans alloc.within
  simp only [persistent, Fin.val_natAdd] at hv
  omega

/-- The moment arithmetic uses the target modulus and target scalar width.
Source-ring row construction has its own earlier allocation. -/
def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 352) : Fin (totalStacks es) :=
  if i = 5 then persistent es 12 else if i = 10 then persistent es 13 else baseMap alloc i

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  by_cases hi5 : i = 5 <;> by_cases hj5 : j = 5
  · exact hi5.trans hj5.symm
  · subst i
    by_cases hj10 : j = 10
    · subst j
      simp [stackMap] at h
    · have he : persistent es 12 = baseMap alloc j := by simp [stackMap, hj5, hj10] at h; exact h
      exact False.elim (baseMap_ne_persistent alloc j 12 he.symm)
  · subst j
    by_cases hi10 : i = 10
    · subst i
      simp [stackMap] at h
    · have he : baseMap alloc i = persistent es 12 := by simp [stackMap, hi5, hi10] at h; exact h
      exact False.elim (baseMap_ne_persistent alloc i 12 he)
  · by_cases hi10 : i = 10 <;> by_cases hj10 : j = 10
    · exact hi10.trans hj10.symm
    · subst i
      have he : persistent es 13 = baseMap alloc j := by simp [stackMap, hj5, hj10] at h; exact h
      exact False.elim (baseMap_ne_persistent alloc j 13 he.symm)
    · subst j
      have he : baseMap alloc i = persistent es 13 := by simp [stackMap, hi5, hi10] at h; exact h
      exact False.elim (baseMap_ne_persistent alloc i 13 he)
    · apply baseMap_injective alloc
      simpa only [stackMap, ite_eq_right hi5, ite_eq_right hj5, ite_eq_right hi10, ite_eq_right hj10] using h

@[simp] theorem stackMap_modulus {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 5 = persistent es 12 := by simp [stackMap]
@[simp] theorem stackMap_width {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 10 = persistent es 13 := by simp [stackMap]

theorem stackMap_native {es : ℕ} (alloc : Allocation es) (i : Fin 256)
    (h5 : i ≠ 5) (h10 : i ≠ 10) :
    stackMap alloc (i.castAdd 96) = ordinary alloc ⟨i.val, by omega⟩ := by
  have hn5 : i.castAdd 96 ≠ (5 : Fin 352) := by
    intro h; apply h5; exact Fin.ext (congrArg (fun j : Fin 352 => j.val) h)
  have hn10 : i.castAdd 96 ≠ (10 : Fin 352) := by
    intro h; apply h10; exact Fin.ext (congrArg (fun j : Fin 352 => j.val) h)
  simp only [stackMap, ite_eq_right hn5, ite_eq_right hn10, baseMap, Fin.val_castAdd, dite_eq_left i.isLt]

@[simp] theorem stackMap_static {es : ℕ} (alloc : Allocation es) (i : Fin 32) :
    stackMap alloc ⟨256 + i.val, by omega⟩ = master alloc i := by
  have h5 : (⟨256 + i.val, by omega⟩ : Fin 352) ≠ 5 := by intro h; have := congrArg Fin.val h; simp at this; omega
  have h10 : (⟨256 + i.val, by omega⟩ : Fin 352) ≠ 10 := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp only [stackMap, ite_eq_right h5, ite_eq_right h10, baseMap]
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  apply congrArg (master alloc)
  exact Fin.ext (by dsimp only; omega)

@[simp] theorem stackMap_outer {es : ℕ} (alloc : Allocation es) (i : Fin 64) :
    stackMap alloc ⟨288 + i.val, by omega⟩ = ordinary alloc ⟨256 + i.val, by omega⟩ := by
  have h5 : (⟨288 + i.val, by omega⟩ : Fin 352) ≠ 5 := by intro h; have := congrArg Fin.val h; simp at this; omega
  have h10 : (⟨288 + i.val, by omega⟩ : Fin 352) ≠ 10 := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp only [stackMap, ite_eq_right h5, ite_eq_right h10, baseMap]
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  apply congrArg (ordinary alloc)
  exact Fin.ext (by dsimp only; omega)

theorem stackMap_avoids_crt {es : ℕ} (alloc : Allocation es)
    (j : Fin (totalStacks es)) (hlo : 320 ≤ j.val) (hhi : j.val < 640) :
    ¬ ∃ i, stackMap alloc i = j := by
  rintro ⟨i, h⟩
  have hv := congrArg Fin.val h
  have hw := alloc.enough.trans alloc.within
  by_cases h5 : i = 5
  · rw [stackMap, ite_eq_left h5] at hv
    change workStacks es + 12 = j.val at hv
    omega
  · by_cases h10 : i = 10
    · rw [stackMap, ite_eq_right h5, ite_eq_left h10] at hv
      change workStacks es + 13 = j.val at hv
      omega
    · rw [stackMap, ite_eq_right h5, ite_eq_right h10] at hv
      by_cases hn : i.val < 256
      · simp only [baseMap, dite_eq_left hn, ordinary] at hv
        omega
      · by_cases hs : i.val < 288
        · simp only [baseMap, dite_eq_right hn, dite_eq_left hs, master_val] at hv
          omega
        · simp only [baseMap, dite_eq_right hn, dite_eq_right hs, ordinary] at hv
          omega

end SubexponentialSAT.SubexpMainMomentPorts

end OAI.Algorithms
