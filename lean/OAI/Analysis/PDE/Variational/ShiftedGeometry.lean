import OAI.Analysis.PDE.Variational.FundamentalDomain

open Set
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem coordinatePeriodShift_not_mem (J : Finset (Fin (m+1))) (L : CellCoordinates m)
    (z : J→ℤ) {i : Fin (m+1)} (hi : i∉J) : coordinatePeriodShift J L z i=0 := by
  change (if hi : i∈J then (z ⟨i,hi⟩:ℝ)*L i else 0)=0
  simp [hi]

theorem exists_translate_in_cell (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (x : CellCoordinates m) (hx : x∈transverseBox J a b) :
    ∃ z : J→ℤ, x+coordinatePeriodShift J (b-a) z ∈ Icc a b := by
  let z : J→ℤ := fun i ↦
    (unique_integer_shift (a i) (x i) (b i-a i) (sub_pos.mpr (hL i i.property))).choose
  have hz (i : J) : a i ≤ (z i:ℝ)*(b i-a i)+x i ∧
      (z i:ℝ)*(b i-a i)+x i<a i+(b i-a i) :=
    (unique_integer_shift (a i) (x i) (b i-a i) (sub_pos.mpr (hL i i.property))).choose_spec.1
  refine ⟨z, ?_, ?_⟩ <;> intro i <;> by_cases hi : i∈J
  · simpa only [Pi.add_apply, coordinatePeriodShift_apply J (b-a) z ⟨i,hi⟩,
      Pi.sub_apply, add_comm] using (hz ⟨i,hi⟩).1
  · simpa only [Pi.add_apply, coordinatePeriodShift_not_mem J (b-a) z hi, add_zero] using (hx i hi).1
  · have h := (hz ⟨i,hi⟩).2.le
    simpa only [Pi.add_apply, coordinatePeriodShift_apply J (b-a) z ⟨i,hi⟩,
      Pi.sub_apply, add_sub_cancel, add_comm] using h
  · simpa only [Pi.add_apply, coordinatePeriodShift_not_mem J (b-a) z hi, add_zero] using (hx i hi).2

theorem coordinate_translate_mem_iff (J : Finset (Fin (m+1))) (L : CellCoordinates m)
    (Ω : Set (CellCoordinates m))
    (hΩ : ∀ z x, x+coordinatePeriodShift J L z ∈ Ω → x∈Ω)
    (z : J→ℤ) (x : CellCoordinates m) :
    x+coordinatePeriodShift J L z ∈ Ω ↔ x∈Ω := by
  refine ⟨hΩ z x, ?_⟩
  intro hx
  apply hΩ (-z) (x+coordinatePeriodShift J L z)
  simpa only [map_neg, add_neg_cancel_right] using hx

theorem face_condition_shifted_cell (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hab : a≤b) (hL : ∀ i∈J, a i<b i)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m))
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z ∈ Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω) :
    ∀ y∈Icc (c∘k.succAbove) (d∘k.succAbove), k.insertNth (d k) y∉Ω := by
  intro y hy hyo
  let x : CellCoordinates m := k.insertNth (d k) y
  have hx : x∈transverseBox J a b := by
    intro i hi
    by_cases hik : i=k
    · subst i
      simp only [x, Fin.insertNth_apply_same, hb k hk]
      exact ⟨hab k,le_rfl⟩
    · obtain ⟨j,rfl⟩ := i.exists_succAbove_eq hik
      simpa only [x, Fin.insertNth_apply_succAbove, Function.comp_apply, ha _ hi, hb _ hi] using
        And.intro (hy.1 j) (hy.2 j)
  obtain ⟨z,hz⟩ := exists_translate_in_cell J a b hL x hx
  let w := x+coordinatePeriodShift J (b-a) z
  have hwk : w k=b k := by
    simp [w,x,coordinatePeriodShift_not_mem J (b-a) z hk,hb k hk]
  have hy' : (fun i ↦ w (k.succAbove i)) ∈ Icc (a∘k.succAbove) (b∘k.succAbove) :=
    ⟨fun i ↦ hz.1 _,fun i ↦ hz.2 _⟩
  have hw : w∈Ω := (coordinate_translate_mem_iff J (b-a) Ω hΩ z x).mpr hyo
  apply hface _ hy'
  convert hw using 1
  ext i
  by_cases hi : i=k
  · subst i
    simpa using hwk.symm
  · obtain ⟨j,rfl⟩ := i.exists_succAbove_eq hi
    simp

/-- Every point strictly inside the transverse box lies inside a shifted
fundamental cell, including points on any seam of the original cell. -/
theorem exists_centered_periodic_cell (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hab : a≤b) (hL : ∀ i∈J, a i<b i) (x : CellCoordinates m)
    (hx : ∀ i, i∉J → a i<x i ∧ x i<b i) :
    ∃ c d : CellCoordinates m, c≤d ∧ d-c=b-a ∧
      (∀ i, i∉J → c i=a i) ∧ (∀ i, i∉J → d i=b i) ∧ x∈cellInterior c d := by
  let c : CellCoordinates m := fun i ↦ if i∈J then x i-(b i-a i)/2 else a i
  let d : CellCoordinates m := fun i ↦ if i∈J then x i+(b i-a i)/2 else b i
  refine ⟨c,d,?_,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i∈J
    · simp only [c,d,ite_eq_left hi]
      have := hL i hi
      linarith
    · simpa only [c,d,ite_eq_right hi] using hab i
  · ext i
    by_cases hi : i∈J <;> simp [c,d,hi]
  · intro i hi; simp only [c,ite_eq_right hi]
  · intro i hi; simp only [d,ite_eq_right hi]
  · intro i
    by_cases hi : i∈J
    · simp only [c,d,ite_eq_left hi]
      have := hL i hi
      constructor <;> linarith
    · simpa only [c,d,ite_eq_right hi] using hx i hi

end OAI.Analysis.PDE.Variational
