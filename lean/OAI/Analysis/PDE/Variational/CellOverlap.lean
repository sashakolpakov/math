import OAI.Analysis.PDE.Variational.CellIsometry
import OAI.Analysis.PDE.Variational.LocalizedEquation

open Set _root_.MeasureTheory
open scoped ContDiff
noncomputable section

namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

/-- The completed values and gradients in different cells agree after any
smooth localization supported in their overlap. -/
theorem cutoff_periodicCellIsometry
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hab : a≤b) (hcd : c≤d)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (hface' : ∀ y∈Icc (c∘k.succAbove) (d∘k.succAbove), k.insertNth (d k) y∉Ω)
    (η : CellCoordinates m→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hcell : tsupport η ⊆ Icc a b ∩ Icc c d)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) :
    OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK
      (periodicH1Pair c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u)) =
    OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK (periodicH1Pair a b Ω _ u) := by
  let T := periodicCellIsometry J a b c d hL hlen ha hb Ω
  let C := OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK
  have heq := (denseRange_periodicTestEmbedding a b Ω (coordinatePeriodSet J (b-a))).equalizer
    (C.continuous.comp ((periodicH1Pair c d Ω _).continuous.comp T.continuous))
    (C.continuous.comp (periodicH1Pair a b Ω _).continuous)
    (funext fun v ↦ by
      simp only [Function.comp_apply]
      change C (periodicH1Pair c d Ω _
        (periodicCellIsometry J a b c d hL hlen ha hb Ω (periodicTestEmbedding a b Ω _ v))) = _
      rw [periodicCellIsometry_test]
      exact (cutoff_periodicH1Pair_test c d hcd Ω _ k hface' η hη hc
        (fun x hx ↦ (hcell hx).2) hM hK v).trans
        (cutoff_periodicH1Pair_test a b hab Ω _ k hface η hη hc
          (fun x hx ↦ (hcell hx).1) hM hK v).symm)
  exact congrFun heq u

theorem periodicCellIsometry_local_agreement
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hab : a≤b) (hcd : c≤d)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (hface' : ∀ y∈Icc (c∘k.succAbove) (d∘k.succAbove), k.insertNth (d k) y∉Ω)
    (η : CellCoordinates m→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hcell : tsupport η ⊆ Icc a b ∩ Icc c d)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K)
    (V : Set (CellCoordinates m)) (hV : IsOpen V) (hone : ∀ x∈V, η x=1)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) :
    ∀ᵐ x ∂volume, x∈V →
      (periodicH1Pair c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u)).1 x =
        (periodicH1Pair a b Ω _ u).1 x ∧
      (periodicH1Pair c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u)).2 x =
        (periodicH1Pair a b Ω _ u).2 x := by
  have heq := cutoff_periodicCellIsometry J a b c d hab hcd hL hlen ha hb Ω k
    hface hface' η hη hc hcell hM hK u
  have hv := cutoffH1Pair_eq_on V hV η (hη.of_le (by simp)) hM hK hone
    (periodicH1Pair c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u))
  have hu := cutoffH1Pair_eq_on V hV η (hη.of_le (by simp)) hM hK hone
    (periodicH1Pair a b Ω _ u)
  rw [heq] at hv
  filter_upwards [hv,hu] with x hx hy
  intro hxo
  exact ⟨(hx hxo).1.symm.trans (hy hxo).1, (hx hxo).2.symm.trans (hy hxo).2⟩

end OAI.Analysis.PDE.Variational
