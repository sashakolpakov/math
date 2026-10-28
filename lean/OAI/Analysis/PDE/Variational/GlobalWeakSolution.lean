import OAI.Analysis.PDE.Variational.EquationLocality
import OAI.Analysis.PDE.Variational.PeriodicLocalL2
import OAI.Analysis.PDE.Variational.PeriodicEquation

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem periodicRepresentative_equation_global
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω⊆transverseInterior J a b)
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A volume) {M : ℝ} (hM : 0≤M)
    (hAM : ∀ᵐ x ∂volume, ‖A x‖≤M)
    (hAp : ∀ z x, A (x+coordinatePeriodShift J (b-a) z)=A x)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (hu : ∀ φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
        ∫ x in Icc a b, f x*φ.val x) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ A x (periodicRepresentative J a b u.val x))
      (periodicRepresentative J a b f) := by
  have hload : ∀ φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
        ∫ x in Icc a b, periodicRepresentative J a b f x*φ.val x := by
    intro φ
    rw [hu φ]
    apply integral_congr_ae
    filter_upwards [coordinateWrap_ae_eq_self J a b hL] with x hx
    simp only [periodicRepresentative,Function.comp_apply,hx,id_eq]
  apply weakEquation_of_local
    ((locallyIntegrableOn_periodicFlux J a b hab hL A hA hAM u.val).mono_set htrans)
    ((locallyIntegrableOn_periodicRepresentative J a b hab hL f).mono_set htrans)
  intro x hx
  obtain ⟨c,d,hcd,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x (htrans hx)
  refine ⟨Ω∩cellInterior c d,hopen.inter (isOpen_cellInterior c d),⟨hx,hxc⟩,inter_subset_left,?_⟩
  exact periodicRepresentative_equation_on_cell J a b c d hL hlen ha hb Ω hΩ A
    hA.restrict hA.restrict hM hM (ae_restrict_of_ae hAM) (ae_restrict_of_ae hAM) hAp
    (periodicRepresentative J a b f)
    (memLp_periodicRepresentative_cell J a b c d hL hlen ha hb f)
    (periodicRepresentative_periodic J a b hL f) u hload

/-- Actual global periodic weak Dirichlet solvability. The value and gradient
come from the completed smooth zero-boundary test space; the global PDE is
proved across all fundamental-cell seams. -/
theorem exists_global_periodic_weak_solution
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω⊆transverseInterior J a b)
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A volume) {M lam : ℝ} (hM : 0≤M)
    (hAM : ∀ᵐ x ∂volume, ‖A x‖≤M) (hlam : 0<lam)
    (hell : ∀ᵐ x ∂volume, ∀ v : CellVectors m, lam*‖v‖^2 ≤ inner ℝ v (A x v))
    (hAp : ∀ z x, A (x+coordinatePeriodShift J (b-a) z)=A x)
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ∃ u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)),
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ A x (periodicRepresentative J a b u.val x))
        (periodicRepresentative J a b f) ∧
      lam*‖u‖≤(2*(b k-a k))*‖f‖ := by
  obtain ⟨u,hu,hbound⟩ := exists_periodic_weak_solution a b hab Ω (coordinatePeriodSet J (b-a))
    k hface A hA.restrict hM (ae_restrict_of_ae hAM) hlam (ae_restrict_of_ae hell) f
  exact ⟨u,periodicRepresentative_equation_global J a b hab hL Ω hopen htrans hΩ A hA hM
    hAM hAp f u hu,hbound⟩

end OAI.Analysis.PDE.Variational
