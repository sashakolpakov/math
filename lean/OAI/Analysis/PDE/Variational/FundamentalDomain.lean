import OAI.Analysis.PDE.Variational.PeriodizedTests

open Set _root_.MeasureTheory
open scoped Pointwise
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

abbrev CoordinatePeriodGroup (J : Finset (Fin (m+1))) (L : CellCoordinates m) :=
  ↥(coordinatePeriodShift J L).range

def periodicStrip (J : Finset (Fin (m+1))) (a L : CellCoordinates m) :
    Set (CellCoordinates m) := {x | ∀ i∈J, a i ≤ x i ∧ x i < a i + L i}

theorem measurableSet_periodicStrip (J : Finset (Fin (m+1)))
    (a L : CellCoordinates m) : MeasurableSet (periodicStrip J a L) := by
  simp only [periodicStrip, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem unique_integer_shift (a x L : ℝ) (hL : 0<L) :
    ∃! k : ℤ, a ≤ (k:ℝ)*L+x ∧ (k:ℝ)*L+x < a+L := by
  refine ⟨-⌊(x-a)/L⌋, ?_, ?_⟩
  · have h₀ := Int.floor_le ((x-a)/L)
    have h₁ := Int.lt_floor_add_one ((x-a)/L)
    have heq : (x-a)/L*L = x-a := div_mul_cancel₀ _ hL.ne'
    have h₂ := mul_le_mul_of_nonneg_right h₀ hL.le
    have h₃ := mul_lt_mul_of_pos_right h₁ hL
    simp only [Int.cast_neg]
    constructor <;> nlinarith
  · intro k hk
    have heq : (x-a)/L*L = x-a := div_mul_cancel₀ _ hL.ne'
    have hf : ⌊(x-a)/L⌋ = -k := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_neg]
      constructor
      · apply (mul_le_mul_iff_left₀ hL).mp
        nlinarith [hk.1]
      · apply (mul_lt_mul_iff_left₀ hL).mp
        nlinarith [hk.2]
    omega

theorem isAddFundamentalDomain_periodicStrip (J : Finset (Fin (m+1)))
    (a L : CellCoordinates m) (hL : ∀ i∈J, 0<L i) :
    IsAddFundamentalDomain (CoordinatePeriodGroup J L) (periodicStrip J a L) volume := by
  apply IsAddFundamentalDomain.mk' (measurableSet_periodicStrip J a L).nullMeasurableSet
  intro x
  let z : J → ℤ := fun i ↦ (unique_integer_shift (a i) (x i) (L i) (hL i i.property)).choose
  have hz (i : J) : a i ≤ (z i:ℝ)*L i+x i ∧ (z i:ℝ)*L i+x i<a i+L i :=
    (unique_integer_shift (a i) (x i) (L i) (hL i i.property)).choose_spec.1
  refine ⟨⟨coordinatePeriodShift J L z, z, rfl⟩, ?_, ?_⟩
  · intro i hi
    change a i ≤ (coordinatePeriodShift J L z + x) i ∧
      (coordinatePeriodShift J L z + x) i < a i+L i
    simp only [Pi.add_apply]
    rw [show coordinatePeriodShift J L z i = (z ⟨i,hi⟩:ℝ)*L i from
      coordinatePeriodShift_apply J L z ⟨i,hi⟩]
    exact hz ⟨i,hi⟩
  · rintro ⟨g, w, rfl⟩ hg
    have hw : w = z := by
      funext i
      apply (unique_integer_shift (a i) (x i) (L i) (hL i i.property)).choose_spec.2
      specialize hg i i.property
      change a i ≤ (coordinatePeriodShift J L w + x) i ∧
        (coordinatePeriodShift J L w + x) i < a i+L i at hg
      simpa only [Pi.add_apply, coordinatePeriodShift_apply] using hg
    apply Subtype.ext
    exact congrArg (coordinatePeriodShift J L) hw

theorem periodicStrip_integral_eq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a c L : CellCoordinates m) (hL : ∀ i∈J, 0<L i)
    (f : CellCoordinates m → H)
    (hf : ∀ z x, f (x+coordinatePeriodShift J L z)=f x) :
    (∫ x in periodicStrip J a L, f x) = ∫ x in periodicStrip J c L, f x := by
  have hcount : (Set.range (coordinatePeriodShift J L)).Countable := Set.countable_range _
  let : Countable (CoordinatePeriodGroup J L) := hcount.to_subtype
  let : VAddInvariantMeasure (CoordinatePeriodGroup J L) (CellCoordinates m) volume :=
    ⟨fun g s _ ↦ measure_preimage_add _ _ _⟩
  apply (isAddFundamentalDomain_periodicStrip J a L hL).setIntegral_eq
    (isAddFundamentalDomain_periodicStrip J c L hL)
  rintro ⟨g, z, rfl⟩ x
  change f (coordinatePeriodShift J L z+x)=f x
  simpa only [add_comm] using hf z x

def transverseBox (J : Finset (Fin (m+1))) (a b : CellCoordinates m) :
    Set (CellCoordinates m) := {x | ∀ i, i∉J → a i≤x i ∧ x i≤b i}

theorem measurableSet_transverseBox (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) : MeasurableSet (transverseBox J a b) := by
  simp only [transverseBox, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    (measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_le (measurable_pi_apply i) measurable_const)

theorem transverseBox_add_shift (J : Finset (Fin (m+1)))
    (a b L : CellCoordinates m) (z : J→ℤ) (x : CellCoordinates m) :
    x+coordinatePeriodShift J L z ∈ transverseBox J a b ↔ x∈transverseBox J a b := by
  have hz (i : Fin (m+1)) (hi : i∉J) : coordinatePeriodShift J L z i=0 := by
    change (if hi : i∈J then (z ⟨i,hi⟩:ℝ)*L i else 0)=0
    simp only [dite_eq_right hi]
  simp only [transverseBox, Set.mem_ofPred_eq, Pi.add_apply]
  constructor <;> intro h i hi <;> simpa only [hz i hi, add_zero] using h i hi

theorem transverseBox_inter_periodicStrip_ae (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) :
    transverseBox J a b ∩ periodicStrip J a (b-a) =ᵐ[volume] Icc a b := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp (ae_cellInterior a b)
  filter_upwards [h] with x hx
  apply propext
  constructor
  · intro hmem
    constructor <;> intro i <;> by_cases hi : i∈J
    · exact (hmem.2 i hi).1
    · exact (hmem.1 i hi).1
    · have := (hmem.2 i hi).2; simp only [Pi.sub_apply] at this; linarith
    · exact (hmem.1 i hi).2
  · intro hmem
    refine ⟨fun i hi ↦ ⟨hmem.1 i,hmem.2 i⟩, ?_⟩
    intro i hi
    exact ⟨hmem.1 i, by simpa only [Pi.sub_apply, add_sub_cancel] using (hx hmem i).2⟩

theorem integral_transverseBox_indicator_strip {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (f : CellCoordinates m→H) :
    (∫ x in periodicStrip J a (b-a), (transverseBox J a b).indicator f x) =
      ∫ x in Icc a b, f x := by
  rw [integral_indicator (measurableSet_transverseBox J a b),
    Measure.restrict_restrict (measurableSet_transverseBox J a b),
    Measure.restrict_congr_set (transverseBox_inter_periodicStrip_ae J a b)]

/-- A periodic integral is independent of the choice of its periodic-coordinate
cell origin; the transverse-coordinate intervals are kept fixed. -/
theorem periodic_cell_integral_eq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (f : CellCoordinates m→H)
    (hf : ∀ z x, f (x+coordinatePeriodShift J (b-a) z)=f x) :
    (∫ x in Icc a b, f x) = ∫ x in Icc c d, f x := by
  have ht : transverseBox J c d=transverseBox J a b := by
    ext x
    constructor <;> intro hx i hi
    · simpa only [ha i hi, hb i hi] using hx i hi
    · simpa only [ha i hi, hb i hi] using hx i hi
  have hp (z : J→ℤ) (x : CellCoordinates m) :
      (transverseBox J a b).indicator f (x+coordinatePeriodShift J (b-a) z)=
        (transverseBox J a b).indicator f x := by
    have hm := transverseBox_add_shift J a b (b-a) z x
    by_cases hx : x∈transverseBox J a b
    · simp only [indicator_of_mem hx, indicator_of_mem (hm.mpr hx), hf]
    · simp only [indicator_of_notMem hx, indicator_of_notMem (mt hm.mp hx)]
  calc
    _ = ∫ x in periodicStrip J a (b-a), (transverseBox J a b).indicator f x :=
      (integral_transverseBox_indicator_strip J a b f).symm
    _ = ∫ x in periodicStrip J c (b-a), (transverseBox J a b).indicator f x :=
      periodicStrip_integral_eq J a c (b-a) (fun i hi ↦ sub_pos.mpr (hL i hi)) _ hp
    _ = _ := by
      rw [← hlen, ← ht]
      exact integral_transverseBox_indicator_strip J c d f

end OAI.Analysis.PDE.Variational
