import OAI.Analysis.PDE.Weak.Elliptic.H1Neighborhood
import OAI.Analysis.PDE.Weak.Elliptic.L2Differentiated

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- One genuine regularity bootstrap: an H¹ load and C² bounded
coefficients give local H¹ representatives for the second derivatives
of the weak solution. -/
theorem interior_H3_near_point
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 2 A) {M D B lam : ℝ} (hlam : 0 < lam)
    (hM : ∀ x, ‖A x‖ ≤ M)
    (hD : ∀ j x, ‖coefficientPartial A j x‖ ≤ D)
    (hB : ∀ i j x, ‖coefficientPartial (coefficientPartial A j) i x‖ ≤ B)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (fd : Fin (m + 1) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hf : ∀ j, HasWeakDirectionalDerivativeOn volume Ω (Pi.single j 1) f (fd j))
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (p.2 x)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ j : Fin (m + 1), ∃ q : H1Pair m, q ∈ H1Zero univ ∧
        HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.1 q.1 ∧
        HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.2 q.2 ∧
        ∀ i : Fin (m + 1), ∃ r : H1Pair m, r ∈ H1Zero univ ∧
          HasWeakDirectionalDerivativeOn volume V (Pi.single i 1) q.1 r.1 ∧
          HasWeakDirectionalDerivativeOn volume V (Pi.single i 1) q.2 r.2 := by
  obtain ⟨U, hU, hxU, hUΩ, hder⟩ := interior_H1_derivatives_near_point
    A (hA.of_le (by norm_num)) hlam hΩ hell p hp f hweak hx
  choose Q hQ hQv hQg using hder
  have hweakU : WeakDivergenceEquation U (fun x ↦ A x (p.2 x)) f :=
    OAI.Analysis.PDE.Variational.weakEquation_congr_on hweak hUΩ (Eventually.of_forall fun _ _ ↦ rfl)
      (Eventually.of_forall fun _ _ ↦ rfl)
  have hsecond (j : Fin (m + 1)) :
      ∃ W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
        ∀ i : Fin (m + 1), ∃ r : H1Pair m, r ∈ H1Zero univ ∧
          HasWeakDirectionalDerivativeOn volume W (Pi.single i 1) (Q j).1 r.1 ∧
          HasWeakDirectionalDerivativeOn volume W (Pi.single i 1) (Q j).2 r.2 := by
    obtain ⟨F, heq⟩ := differentiated_equation_L2 A hA hM hD hB p.2
      (fun i ↦ (Q i).2) hQg f (fd j) j ((hf j).mono volume hUΩ) hweakU
    exact interior_H1_derivatives_near_point A (hA.of_le (by norm_num)) hlam hU
      (fun y hy z ↦ hell y (hUΩ hy) z) (Q j) (hQ j) F heq hxU
  choose W hW hxW hWU hWr using hsecond
  let V := U ∩ ⋂ j, W j
  have hVU : V ⊆ U := inter_subset_left
  have hVW (j : Fin (m + 1)) : V ⊆ W j := fun y hy ↦ mem_iInter.mp hy.2 j
  refine ⟨V, hU.inter (isOpen_iInter_of_finite hW), ⟨hxU, mem_iInter.mpr hxW⟩,
    hVU.trans hUΩ, ?_⟩
  intro j
  refine ⟨Q j, hQ j, (hQv j).mono volume hVU, (hQg j).mono volume hVU, ?_⟩
  intro i
  obtain ⟨r, hr, hrv, hrg⟩ := hWr j i
  exact ⟨r, hr, hrv.mono volume (hVW j), hrg.mono volume (hVW j)⟩

end OAI.Analysis.PDE.Weak
