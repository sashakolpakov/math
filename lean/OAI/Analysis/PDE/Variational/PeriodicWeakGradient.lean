import OAI.Analysis.PDE.Variational.PeriodicH1

open Set Filter _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem periodicH1Pair_weakGradient
    (a b : CellCoordinates m) (hab : a≤b) (Ω P : Set (CellCoordinates m))
    (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω P) (j : Fin (m+1)) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation (cellInterior a b)
      (coordinateTestVector j (periodicH1Pair a b Ω P u).1)
      (fun x ↦ -((periodicH1Pair a b Ω P u).2 x) j) := by
  intro φ hφ hc hs
  calc
    _ = ∫ x, fderiv ℝ φ x (Pi.single j 1) *
        cellZeroExtension a b (periodicValue a b Ω P u) x := by
      apply integral_congr_ae
      filter_upwards [periodicH1Pair_value_ae a b Ω P u] with x hx
      simp only [inner_coordinateTestVector, cellGradient_apply, hx, mul_comm]
    _ = -(∫ x, φ x * (cellZeroExtension a b u.val x) j) :=
      cellZeroExtension_weak_derivative a b hab Ω P k hface u j (hφ.of_le (by simp)) hs
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [periodicH1Pair_gradient_ae a b Ω P u] with x hx
      rw [hx]
      ring

/-- The explicit periodic gradient is the distributional gradient of the
explicit periodic value on the entire domain, not just off the cell seams. -/
theorem periodicRepresentative_weakGradient_equation
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω⊆transverseInterior J a b)
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) (j : Fin (m+1)) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω
      (coordinateTestVector j (periodicRepresentative J a b (periodicValue a b Ω _ u)))
      (fun x ↦ -(periodicRepresentative J a b u.val x) j) := by
  let L : ℝ →L[ℝ] CellVectors m :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j 1)
  let K : CellVectors m →L[ℝ] ℝ := -(innerSL ℝ (EuclideanSpace.single j 1))
  have hH := L.locallyIntegrableOn_comp
    ((locallyIntegrableOn_periodicRepresentative J a b hab hL (periodicValue a b Ω _ u)).mono_set htrans)
  have hf := K.locallyIntegrableOn_comp
    ((locallyIntegrableOn_periodicRepresentative J a b hab hL u.val).mono_set htrans)
  change LocallyIntegrableOn
    (coordinateTestVector j (periodicRepresentative J a b (periodicValue a b Ω _ u))) Ω volume at hH
  have hf' : LocallyIntegrableOn (fun x ↦ -(periodicRepresentative J a b u.val x) j) Ω volume := by
    simpa [K, Function.comp_def, EuclideanSpace.inner_single_left] using hf
  apply weakEquation_of_local hH hf'
  intro x hx
  obtain ⟨c,d,hcd,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x (htrans hx)
  have hface' := face_condition_shifted_cell J a b c d hab hL ha hb Ω hΩ k hk hface
  let v := periodicCellIsometry J a b c d hL hlen ha hb Ω u
  have hagree := periodicH1Pair_shifted_ae J a b c d hab hcd hL hlen ha hb Ω k hface hface' u
  refine ⟨Ω∩cellInterior c d,hopen.inter (isOpen_cellInterior c d),⟨hx,hxc⟩,inter_subset_left,?_⟩
  apply weakEquation_congr_on (periodicH1Pair_weakGradient c d hcd Ω _ k hface' v j) inter_subset_right
  · filter_upwards [hagree] with y hy
    intro hyU
    dsimp only [coordinateTestVector, v]
    rw [(hy (cellInterior_subset_Icc c d hyU.2)).1]
  · filter_upwards [hagree] with y hy
    intro hyU
    rw [← (hy (cellInterior_subset_Icc c d hyU.2)).2]

theorem periodicRepresentative_weak_derivative
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω⊆transverseInterior J a b)
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) (j : Fin (m+1))
    (φ : CellCoordinates m→ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ⊆Ω) :
    (∫ x, fderiv ℝ φ x (Pi.single j 1) *
      periodicRepresentative J a b (periodicValue a b Ω _ u) x) =
      -(∫ x, φ x * (periodicRepresentative J a b u.val x) j) := by
  have h := periodicRepresentative_weakGradient_equation J a b hab hL Ω hopen htrans hΩ
    k hk hface u j φ hφ hc hs
  simpa only [inner_coordinateTestVector, cellGradient_apply, neg_mul, mul_neg, integral_neg, mul_comm] using h

end OAI.Analysis.PDE.Variational
