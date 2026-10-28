import OAI.Analysis.PDE.Variational.CellIsometry
import OAI.Analysis.PDE.Variational.LocalEquation

open Set _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem testGradientMap_ae (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (φ : PeriodicTests Ω P) :
    (fun x ↦ testGradientMap a b Ω P φ x) =ᵐ[volume.restrict (Icc a b)] cellGradient φ :=
  (memLp_continuous_cell a b (continuous_cellGradient (periodicTest_contDiff_one φ))).coeFn_toLp

def testCoefficientPairing (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (φ : PeriodicTests Ω P) : PeriodicH10 a b Ω P →L[ℝ] ℝ :=
  (OAI.Analysis.PDE.Dirichlet.coefficientEnergy A hA hM hAM (testGradientMap a b Ω P φ)).comp
    (testGradientMap a b Ω P).range.topologicalClosure.subtypeL

theorem testCoefficientPairing_eq (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (φ : PeriodicTests Ω P) (u : PeriodicH10 a b Ω P) :
    testCoefficientPairing a b Ω P A hA hM hAM φ u =
      ∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x)) := by
  calc
    _ = OAI.Analysis.PDE.Dirichlet.coefficientEnergy A hA hM hAM (testGradientMap a b Ω P φ) u.val := rfl
    _ = ∫ x in Icc a b, inner ℝ (testGradientMap a b Ω P φ x) (A x (u.val x)) :=
      OAI.Analysis.PDE.Dirichlet.coefficientEnergy_eq_integral A hA hM hAM _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [testGradientMap_ae a b Ω P φ] with x hx
      rw [hx]

theorem testCoefficientPairing_test (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (φ ψ : PeriodicTests Ω P) :
    testCoefficientPairing a b Ω P A hA hM hAM φ (periodicTestEmbedding a b Ω P ψ) =
      ∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (cellGradient ψ x)) := by
  rw [testCoefficientPairing_eq]
  apply integral_congr_ae
  filter_upwards [testGradientMap_ae a b Ω P ψ] with x hx
  change inner ℝ (cellGradient φ x) (A x (testGradientMap a b Ω P ψ x)) = _
  rw [hx]

theorem periodicCellIsometry_pairing
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hAa : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hAc : AEStronglyMeasurable A (volume.restrict (Icc c d)))
    {M N : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (hAN : ∀ᵐ x ∂volume.restrict (Icc c d), ‖A x‖≤N)
    (hAp : ∀ z x, A (x+coordinatePeriodShift J (b-a) z)=A x)
    (φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)))
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) :
    (∫ x in Icc c d, inner ℝ (cellGradient φ x)
      (A x ((periodicCellIsometry J a b c d hL hlen ha hb Ω u).val x))) =
      ∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x)) := by
  let T := periodicCellIsometry J a b c d hL hlen ha hb Ω
  let F := testCoefficientPairing c d Ω _ A hAc hN hAN φ
  let G := testCoefficientPairing a b Ω _ A hAa hM hAM φ
  have heq := (denseRange_periodicTestEmbedding a b Ω (coordinatePeriodSet J (b-a))).equalizer
    (F.continuous.comp T.continuous) G.continuous (funext fun ψ ↦ by
      simp only [Function.comp_apply]
      change testCoefficientPairing c d Ω _ A hAc hN hAN φ
        (periodicCellIsometry J a b c d hL hlen ha hb Ω (periodicTestEmbedding a b Ω _ ψ)) =
        testCoefficientPairing a b Ω _ A hAa hM hAM φ (periodicTestEmbedding a b Ω _ ψ)
      rw [periodicCellIsometry_test, testCoefficientPairing_test, testCoefficientPairing_test]
      apply (periodic_cell_integral_eq J a b c d hL hlen ha hb _ _).symm
      intro z x
      rw [hAp, cellGradient_periodic (φ.property.2.2 _ ⟨z,rfl⟩),
        cellGradient_periodic (ψ.property.2.2 _ ⟨z,rfl⟩)])
  have hu := congrFun heq u
  change testCoefficientPairing c d Ω _ A hAc hN hAN φ (T u) =
    testCoefficientPairing a b Ω _ A hAa hM hAM φ u at hu
  simpa only [testCoefficientPairing_eq] using hu

/-- The same periodic weak solution solves the weak equation in every shifted
fundamental cell, including cells whose interiors cross the original seams. -/
theorem periodicCellIsometry_weak_test
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hAa : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hAc : AEStronglyMeasurable A (volume.restrict (Icc c d)))
    {M N : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (hAN : ∀ᵐ x ∂volume.restrict (Icc c d), ‖A x‖≤N)
    (hAp : ∀ z x, A (x+coordinatePeriodShift J (b-a) z)=A x)
    (f : CellCoordinates m→ℝ) (hfp : ∀ z x, f (x+coordinatePeriodShift J (b-a) z)=f x)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (hu : ∀ φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
        ∫ x in Icc a b, f x*φ.val x)
    (φ : PeriodicTests Ω (coordinatePeriodSet J (b-a))) :
    (∫ x in Icc c d, inner ℝ (cellGradient φ x)
      (A x ((periodicCellIsometry J a b c d hL hlen ha hb Ω u).val x))) =
      ∫ x in Icc c d, f x*φ.val x := by
  rw [periodicCellIsometry_pairing J a b c d hL hlen ha hb Ω A hAa hAc hM hN hAM hAN hAp,
    hu φ]
  apply periodic_cell_integral_eq J a b c d hL hlen ha hb
  intro z x
  rw [hfp, φ.property.2.2 _ ⟨z,rfl⟩]

end OAI.Analysis.PDE.Variational
