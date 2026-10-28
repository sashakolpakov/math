import OAI.Analysis.PDE.Variational.FundamentalDomain

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem periodicStrip_lintegral_eq
    (J : Finset (Fin (m+1))) (a c L : CellCoordinates m) (hL : ∀ i∈J, 0<L i)
    (f : CellCoordinates m → ℝ≥0∞)
    (hf : ∀ z x, f (x+coordinatePeriodShift J L z)=f x) :
    (∫⁻ x in periodicStrip J a L, f x) = ∫⁻ x in periodicStrip J c L, f x := by
  have hcount : (Set.range (coordinatePeriodShift J L)).Countable := Set.countable_range _
  let : Countable (CoordinatePeriodGroup J L) := hcount.to_subtype
  let : VAddInvariantMeasure (CoordinatePeriodGroup J L) (CellCoordinates m) volume :=
    ⟨fun g s _ ↦ measure_preimage_add _ _ _⟩
  apply (isAddFundamentalDomain_periodicStrip J a L hL).setLIntegral_eq
    (isAddFundamentalDomain_periodicStrip J c L hL) f
  rintro ⟨g, z, rfl⟩ x
  change f (coordinatePeriodShift J L z+x)=f x
  simpa only [add_comm] using hf z x

theorem lintegral_transverseBox_indicator_strip
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (f : CellCoordinates m→ℝ≥0∞) :
    (∫⁻ x in periodicStrip J a (b-a), (transverseBox J a b).indicator f x) =
      ∫⁻ x in Icc a b, f x := by
  rw [lintegral_indicator (measurableSet_transverseBox J a b),
    Measure.restrict_restrict (measurableSet_transverseBox J a b),
    Measure.restrict_congr_set (transverseBox_inter_periodicStrip_ae J a b)]

theorem periodic_cell_lintegral_eq
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (f : CellCoordinates m→ℝ≥0∞)
    (hf : ∀ z x, f (x+coordinatePeriodShift J (b-a) z)=f x) :
    (∫⁻ x in Icc a b, f x) = ∫⁻ x in Icc c d, f x := by
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
    _ = ∫⁻ x in periodicStrip J a (b-a), (transverseBox J a b).indicator f x :=
      (lintegral_transverseBox_indicator_strip J a b f).symm
    _ = ∫⁻ x in periodicStrip J c (b-a), (transverseBox J a b).indicator f x :=
      periodicStrip_lintegral_eq J a c (b-a) (fun i hi ↦ sub_pos.mpr (hL i hi)) _ hp
    _ = _ := by
      rw [← hlen, ← ht]
      exact lintegral_transverseBox_indicator_strip J c d f

end OAI.Analysis.PDE.Variational
