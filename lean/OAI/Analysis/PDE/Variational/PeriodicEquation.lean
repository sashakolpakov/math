import OAI.Analysis.PDE.Variational.PeriodicRepresentative
import OAI.Analysis.PDE.Variational.CellEquation
import OAI.Analysis.PDE.Variational.LocalizedEquation
import OAI.Analysis.PDE.Variational.ShiftedGeometry

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

/-- The single explicit periodic gradient solves the actual PDE on every
shifted open cell, not merely on the original fundamental-cell interior. -/
theorem periodicRepresentative_equation_on_cell
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m))
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hAa : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hAc : AEStronglyMeasurable A (volume.restrict (Icc c d)))
    {M N : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (hAN : ∀ᵐ x ∂volume.restrict (Icc c d), ‖A x‖≤N)
    (hAp : ∀ z x, A (x+coordinatePeriodShift J (b-a) z)=A x)
    (f : CellCoordinates m→ℝ) (hf : MemLp f 2 (volume.restrict (Icc c d)))
    (hfp : ∀ z x, f (x+coordinatePeriodShift J (b-a) z)=f x)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (hu : ∀ φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
        ∫ x in Icc a b, f x*φ.val x) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩cellInterior c d)
      (fun x ↦ A x (periodicRepresentative J a b u.val x)) f := by
  let v := periodicCellIsometry J a b c d hL hlen ha hb Ω u
  have hv : ∀ φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc c d, inner ℝ (cellGradient φ x) (A x (v.val x))) =
        ∫ x in Icc c d, hf.toLp f x*φ.val x := by
    intro φ
    rw [periodicCellIsometry_weak_test J a b c d hL hlen ha hb Ω A hAa hAc hM hN
      hAM hAN hAp f hfp u hu]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hLc : ∀ i∈J, c i<d i := by
    intro i hi
    have heq := congrFun hlen i
    simp only [Pi.sub_apply] at heq
    linarith [hL i hi]
  have hΩc : ∀ z x, x+coordinatePeriodShift J (d-c) z∈Ω → x∈Ω := by
    simpa only [hlen] using hΩ
  have hloc : ∀ (w : PeriodicH10 c d Ω (coordinatePeriodSet J (b-a))),
      (∀ φ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
        (∫ x in Icc c d, inner ℝ (cellGradient φ x) (A x (w.val x))) =
          ∫ x in Icc c d, hf.toLp f x * φ.val x) →
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩cellInterior c d)
        (coefficientCellFlux c d Ω (coordinatePeriodSet J (b-a)) A hAc hN hAN w)
        (cellZeroExtension c d (hf.toLp f)) := by
    rw [← hlen]
    exact coefficientCellFlux_localEquation J c d hLc Ω hΩc A hAc hN hAN (hf.toLp f)
  apply weakEquation_congr_on (hloc v hv) Subset.rfl
  · have hvg : v.val =ᵐ[volume.restrict (Icc c d)] periodicRepresentative J a b u.val := by
      dsimp only [v]
      rw [periodicCellIsometry_gradient_pullback]
      exact periodicCellPullback_ae J a b c d hL hlen ha hb u.val
    have hvg' := (ae_restrict_iff' measurableSet_Icc).mp hvg
    filter_upwards [hvg',coefficientCellFlux_ae c d Ω (coordinatePeriodSet J (b-a)) A hAc hN hAN v]
      with x hx hflux
    intro hxo
    have hxc := cellInterior_subset_Icc c d hxo.2
    rw [hflux]
    simp only [cellZeroExtension,indicator_of_mem hxc,hx hxc]
  · have hfc := (ae_restrict_iff' measurableSet_Icc).mp hf.coeFn_toLp
    filter_upwards [hfc] with x hx
    intro hxo
    have hxc := cellInterior_subset_Icc c d hxo.2
    simp only [cellZeroExtension,indicator_of_mem hxc]
    exact (hx hxc).symm

end OAI.Analysis.PDE.Variational
