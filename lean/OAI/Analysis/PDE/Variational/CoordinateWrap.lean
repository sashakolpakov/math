import OAI.Analysis.PDE.Variational.CellLIntegral

open Set Filter _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The canonical, measurable representative modulo the rectangular lattice. -/
def coordinateWrap (J : Finset (Fin (m+1))) (a L : CellCoordinates m)
    (x : CellCoordinates m) : CellCoordinates m :=
  fun i ↦ if i∈J then x i-(⌊(x i-a i)/L i⌋:ℝ)*L i else x i

theorem measurable_coordinateWrap (J : Finset (Fin (m+1))) (a L : CellCoordinates m) :
    Measurable (coordinateWrap J a L) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈J
  · simp only [coordinateWrap,ite_eq_left hi]
    fun_prop
  · simpa only [coordinateWrap,ite_eq_right hi] using measurable_pi_apply i

theorem coordinateWrap_eq_add_shift (J : Finset (Fin (m+1))) (a L x : CellCoordinates m) :
    coordinateWrap J a L x =
      x+coordinatePeriodShift J L (fun i ↦ -⌊(x i-a i)/L i⌋) := by
  ext i
  by_cases hi : i∈J
  · change (if i∈J then _ else _) = x i+(if hi : i∈J then _ else _)
    simp [hi, sub_eq_add_neg]
  · change (if i∈J then _ else _) = x i+(if hi : i∈J then _ else _)
    simp [hi]

theorem coordinateWrap_periodic (J : Finset (Fin (m+1))) (a L : CellCoordinates m)
    (hL : ∀ i∈J, 0<L i) (z : J→ℤ) (x : CellCoordinates m) :
    coordinateWrap J a L (x+coordinatePeriodShift J L z)=coordinateWrap J a L x := by
  ext i
  by_cases hi : i∈J
  · have hLi := (hL i hi).ne'
    have hs : coordinatePeriodShift J L z i=(z ⟨i,hi⟩:ℝ)*L i :=
      coordinatePeriodShift_apply J L z ⟨i,hi⟩
    simp only [coordinateWrap,ite_eq_left hi,Pi.add_apply,hs]
    have heq : (x i+(z ⟨i,hi⟩:ℝ)*L i-a i)/L i = (x i-a i)/L i+(z ⟨i,hi⟩:ℝ) := by
      field_simp
      ring
    rw [heq,Int.floor_add_intCast,Int.cast_add]
    ring
  · have hs : coordinatePeriodShift J L z i=0 := by
      change (if hi : i∈J then _ else _)=0
      simp [hi]
    simp only [coordinateWrap,ite_eq_right hi,Pi.add_apply,hs,add_zero]

theorem coordinateWrap_eq_self (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) {x : CellCoordinates m} (hx : x∈cellInterior a b) :
    coordinateWrap J a (b-a) x=x := by
  ext i
  by_cases hi : i∈J
  · have hLi : 0<b i-a i := sub_pos.mpr (hL i hi)
    have hf : ⌊(x i-a i)/(b i-a i)⌋=0 := by
      apply Int.floor_eq_zero_iff.mpr
      refine ⟨div_nonneg (sub_nonneg.mpr (hx i).1.le) hLi.le, ?_⟩
      apply (div_lt_one hLi).mpr
      linarith [(hx i).2]
    simp only [coordinateWrap,ite_eq_left hi,Pi.sub_apply,hf,Int.cast_zero,zero_mul,sub_zero]
  · simp only [coordinateWrap,ite_eq_right hi]

theorem coordinateWrap_ae_eq_self (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) :
    coordinateWrap J a (b-a) =ᵐ[volume.restrict (Icc a b)] id := by
  filter_upwards [ae_cellInterior a b] with x hx
  exact coordinateWrap_eq_self J a b hL hx

/-- Wrapping any shifted cell into the reference cell preserves Lebesgue
measure. In particular this respects all L² equivalence classes. -/
theorem measurePreserving_coordinateWrap
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i) :
    MeasurePreserving (coordinateWrap J a (b-a))
      (volume.restrict (Icc c d)) (volume.restrict (Icc a b)) := by
  refine ⟨measurable_coordinateWrap J a (b-a), ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_coordinateWrap J a (b-a)) hs]
  have hperiod (z : J→ℤ) (x : CellCoordinates m) :
      s.indicator (fun _ ↦ (1:ℝ≥0∞)) (coordinateWrap J a (b-a) (x+coordinatePeriodShift J (b-a) z)) =
        s.indicator (fun _ ↦ (1:ℝ≥0∞)) (coordinateWrap J a (b-a) x) := by
    rw [coordinateWrap_periodic J a (b-a) (fun i hi ↦ sub_pos.mpr (hL i hi))]
  have heq := periodic_cell_lintegral_eq J a b c d hL hlen ha hb
    (fun x ↦ s.indicator (fun _ ↦ (1:ℝ≥0∞)) (coordinateWrap J a (b-a) x)) hperiod
  have href : (∫⁻ x in Icc a b, s.indicator (fun _ ↦ (1:ℝ≥0∞))
      (coordinateWrap J a (b-a) x)) = (volume.restrict (Icc a b)) s := by
    calc
      _ = ∫⁻ x in Icc a b, s.indicator (fun _ ↦ (1:ℝ≥0∞)) x := by
        apply lintegral_congr_ae
        filter_upwards [coordinateWrap_ae_eq_self J a b hL] with x hx
        rw [hx]; rfl
      _ = _ := by rw [lintegral_indicator hs]; simp
  rw [href] at heq
  rw [heq]
  change (volume.restrict (Icc c d)) ((coordinateWrap J a (b-a)) ⁻¹' s) = _
  rw [← lintegral_indicator_one ((measurable_coordinateWrap J a (b-a)) hs)]
  congr 1

end OAI.Analysis.PDE.Variational
