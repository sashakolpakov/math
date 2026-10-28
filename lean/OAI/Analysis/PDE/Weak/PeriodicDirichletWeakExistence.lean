import OAI.Analysis.PDE.Weak.Elliptic.GlobalBoundaryCell
import OAI.Analysis.PDE.Variational.GlobalWeakSolution
import OAI.Analysis.PDE.Dirichlet.CoefficientExtension

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Dirichlet

variable {m : ℕ}

theorem periodic_coefficient_bounded_on_domain
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ J, a i < b i) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : Continuous A)
    (hAp : ∀ z x, A (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = A x) :
    ∃ M : ℝ, ∀ x ∈ Ω, ‖A x‖ ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hA.continuousOn
  refine ⟨M,?_⟩
  intro x hx
  obtain ⟨z,hz⟩ := closed_domain_has_cell_representatives J a b hL htrans x (subset_closure hx)
  simpa only [hAp] using hM (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) hz

theorem identityExtendCoefficient_periodic
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hΩ : ∀ z x, x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hAp : ∀ z x, A (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = A x) :
    ∀ z x, OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient Ω A (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) =
      OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient Ω A x := by
  intro z x
  by_cases hx : x ∈ Ω
  · have hz := add_mem_of_backward_invariant (OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a)) hΩ z x hx
    simp only [OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_of_mem Ω A hx,OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_of_mem Ω A hz,hAp]
  · have hz : x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z ∉ Ω := fun h ↦ hx (hΩ z x h)
    simp only [OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_of_not_mem Ω A hx,OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_of_not_mem Ω A hz]

/-- Actual periodic weak existence only assumes coercivity inside the physical
domain. Boundedness follows from periodicity and the compact reference cell;
the coefficient is extended by the identity solely for the variational solve. -/
theorem exists_periodic_weak_solution_of_domain_ellipticity
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i) (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hΩ : ∀ z x, x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (k : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : Continuous A)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ Ω, ∀ z, lam*‖z‖^2 ≤ inner ℝ (A x z) z)
    (hAp : ∀ z x, A (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = A x)
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ∃ u : OAI.Analysis.PDE.Variational.PeriodicH10 a b Ω (OAI.Analysis.PDE.Variational.coordinatePeriodSet J (b-a)),
      WeakDivergenceEquation Ω
        (fun x ↦ A x (OAI.Analysis.PDE.Variational.periodicRepresentative J a b u.val x)) (OAI.Analysis.PDE.Variational.periodicRepresentative J a b f) ∧
      min lam 1*‖u‖ ≤ (2*(b k-a k))*‖f‖ := by
  obtain ⟨M,hM⟩ := periodic_coefficient_bounded_on_domain J a b hL htrans A hA hAp
  have hmeas : AEStronglyMeasurable (OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient Ω A) volume :=
    OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_measurable Ω hopen.measurableSet A hA.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂volume, ‖OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient Ω A x‖ ≤ max M 1 :=
    OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_bound Ω A (Eventually.of_forall hM)
  have hell' : ∀ᵐ x ∂volume, x ∈ Ω → ∀ z : OAI.Analysis.PDE.Variational.CellVectors m,
      lam*‖z‖^2 ≤ inner ℝ z (A x z) := by
    exact Eventually.of_forall fun x hx z ↦ by simpa only [real_inner_comm] using hell x hx z
  obtain ⟨u,hu,hue⟩ := OAI.Analysis.PDE.Variational.exists_global_periodic_weak_solution J a b hab hL Ω hopen htrans hΩ
    k hface (OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient Ω A) hmeas
    (show 0 ≤ max M 1 from le_trans zero_le_one (le_max_right _ _)) hbound
    (lt_min hlam zero_lt_one) (OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_elliptic Ω A hell')
    (identityExtendCoefficient_periodic J a b hΩ A hAp) f
  refine ⟨u,?_,hue⟩
  apply OAI.Analysis.PDE.Variational.weakEquation_congr_on hu Subset.rfl
  · exact Eventually.of_forall fun x hx ↦ by rw [OAI.Analysis.PDE.Dirichlet.identityExtendCoefficient_of_mem Ω A hx]
  · exact Eventually.of_forall fun _ _ ↦ rfl

end OAI.Analysis.PDE.Weak
