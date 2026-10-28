import OAI.Analysis.PDE.Variational.FundamentalDomain
import OAI.Analysis.PDE.Variational.CompletionIsometry

open Set _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem cellGradient_periodic {u : CellCoordinates m→ℝ} {p : CellCoordinates m}
    (h : ∀ x, u (x+p)=u x) (x : CellCoordinates m) :
    cellGradient u (x+p)=cellGradient u x := by
  have heq : (fun x ↦ u (x+p))=u := funext h
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := x) p
  rw [heq] at hd
  ext i
  simp only [cellGradient_apply, hd]

theorem norm_testGradientMap_cell_eq
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m))
    (u : PeriodicTests Ω (coordinatePeriodSet J (b-a))) :
    ‖testGradientMap c d Ω (coordinatePeriodSet J (b-a)) u‖ =
      ‖testGradientMap a b Ω (coordinatePeriodSet J (b-a)) u‖ := by
  have hs : ‖testGradientMap c d Ω (coordinatePeriodSet J (b-a)) u‖^2 =
      ‖testGradientMap a b Ω (coordinatePeriodSet J (b-a)) u‖^2 := by
    change ‖cellToL2 c d (cellGradient u) (continuous_cellGradient (periodicTest_contDiff_one u))‖^2 =
      ‖cellToL2 a b (cellGradient u) (continuous_cellGradient (periodicTest_contDiff_one u))‖^2
    rw [norm_sq_cellToL2, norm_sq_cellToL2]
    apply (periodic_cell_integral_eq J a b c d hL hlen ha hb _ _).symm
    intro z x
    rw [cellGradient_periodic (u.property.2.2 _ ⟨z,rfl⟩)]
  nlinarith [norm_nonneg (testGradientMap c d Ω (coordinatePeriodSet J (b-a)) u),
    norm_nonneg (testGradientMap a b Ω (coordinatePeriodSet J (b-a)) u)]

/-- The true periodic energy space is independent, isometrically, of the
periodic cell origin. Both sides remain completions of actual test gradients. -/
def periodicCellIsometry
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m)) :
    PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)) ≃ₗᵢ[ℝ]
      PeriodicH10 c d Ω (coordinatePeriodSet J (b-a)) :=
  completionIsometry _ _ (norm_testGradientMap_cell_eq J a b c d hL hlen ha hb Ω)

@[simp] theorem periodicCellIsometry_test
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m)) (u : PeriodicTests Ω (coordinatePeriodSet J (b-a))) :
    periodicCellIsometry J a b c d hL hlen ha hb Ω (periodicTestEmbedding a b Ω _ u)=
      periodicTestEmbedding c d Ω _ u := by
  apply completionIsometry_test

end OAI.Analysis.PDE.Variational
