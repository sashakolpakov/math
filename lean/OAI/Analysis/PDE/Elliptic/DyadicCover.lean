import OAI.Analysis.PDE.Elliptic.DyadicNeighborhoods
import Mathlib.Analysis.BoxIntegral.Partition.Measure

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*}

theorem ennreal_mul_lt_self_of_lt_one {a b : ℝ≥0∞}
    (ha : a < 1) (hb : b ≠ 0) (hbt : b ≠ ⊤) : a * b < b := by
  have hat : a ≠ ⊤ := ne_of_lt (ha.trans (by simp))
  apply (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top hat hbt) hbt).mp
  rw [ENNReal.toReal_mul]
  have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb hbt
  have ha' : a.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hat (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mpr ha
  nlinarith

/-- Dyadic covering estimate for open sets. A high-density child
forces its whole parent into `D`; the conclusion is the strict
measure contraction needed for the growth-lemma iteration. -/
theorem dyadic_open_cover_measure [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] (B : Box ι)
    {A D : Set (ι → ℝ)} (hA : IsOpen A) {theta : ℝ≥0∞} (htheta : theta < 1)
    (hpos : ∀ w : List (Set ι), μ (dyadicBox B w : Set (ι → ℝ)) ≠ 0)
    (hroot : μ (A ∩ (B : Set (ι → ℝ))) ≤ theta * μ B)
    (hparent : ∀ (w : List (Set ι)) (s : Set ι),
      theta * μ ((dyadicBox B w).splitCenterBox s : Set (ι → ℝ)) <
        μ (A ∩ ((dyadicBox B w).splitCenterBox s : Set (ι → ℝ))) →
      (dyadicBox B w : Set (ι → ℝ)) ⊆ D) :
    μ (A ∩ (B : Set (ι → ℝ))) ≤ theta * μ D := by
  let P : Box ι → Prop := fun Q ↦ μ (A ∩ (Q : Set (ι → ℝ))) ≤ theta * μ Q
  let S : Set (List (Set ι)) :=
    {w | P (dyadicBox B w) ∧ ∃ s : Set ι, ¬P ((dyadicBox B w).splitCenterBox s)}
  have hcover : A ∩ (B : Set (ι → ℝ)) ⊆ ⋃ w ∈ S, (dyadicBox B w : Set (ι → ℝ)) := by
    intro x hx
    obtain ⟨w, hxw, hwA⟩ := exists_dyadicBox_subset_open B hA hx.2 hx.1
    have hbad : ¬P (dyadicBox B w) := by
      dsimp [P]
      rw [inter_eq_right.mpr hwA]
      exact not_le_of_gt (ennreal_mul_lt_self_of_lt_one htheta (hpos w)
        ((dyadicBox B w).measure_coe_lt_top μ).ne)
    obtain ⟨v, s, hv, hs, hsub⟩ := exists_dyadic_good_parent P B w hroot hbad
    exact mem_iUnion₂.mpr ⟨v, ⟨hv, s, hs⟩,
      (dyadicBox B v).splitCenterBox_le s (hsub hxw)⟩
  apply measure_le_mul_of_ranked_laminar_cover μ
    (fun w : List (Set ι) ↦ (dyadicBox B w : Set (ι → ℝ))) List.length S
    (fun v w hsub hne ↦ dyadicBox_subset_length_lt B v w hsub hne)
    (dyadicBox_laminar B) (fun w ↦ (dyadicBox B w).measurableSet_coe) hcover
  · intro w hw
    obtain ⟨s, hs⟩ := hw.2
    exact hparent w s (lt_of_not_ge hs)
  · intro w hw
    have heq : (A ∩ (B : Set (ι → ℝ))) ∩ (dyadicBox B w : Set (ι → ℝ)) =
        A ∩ (dyadicBox B w : Set (ι → ℝ)) := by
      ext x
      exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩,
        fun hx ↦ ⟨⟨hx.1, dyadicBox_le B w hx.2⟩, hx.2⟩⟩
    rw [heq]
    exact hw.1

theorem box_volume_ne_zero [Fintype ι] (B : Box ι) :
    volume (B : Set (ι → ℝ)) ≠ 0 := by
  have hp : 0 < (volume (B : Set (ι → ℝ))).toReal := by
    rw [Box.volume_apply']
    exact Finset.prod_pos fun i _ ↦ sub_pos.mpr (B.lower_lt_upper i)
  intro hz
  simp [hz] at hp

theorem dyadic_open_cover_volume [Fintype ι] [Nonempty ι] (B : Box ι)
    {A D : Set (ι → ℝ)} (hA : IsOpen A) {theta : ℝ≥0∞} (htheta : theta < 1)
    (hroot : volume (A ∩ (B : Set (ι → ℝ))) ≤ theta * volume (B : Set (ι → ℝ)))
    (hparent : ∀ (w : List (Set ι)) (s : Set ι),
      theta * volume ((dyadicBox B w).splitCenterBox s : Set (ι → ℝ)) <
        volume (A ∩ ((dyadicBox B w).splitCenterBox s : Set (ι → ℝ))) →
      (dyadicBox B w : Set (ι → ℝ)) ⊆ D) :
    volume (A ∩ (B : Set (ι → ℝ))) ≤ theta * volume D :=
  dyadic_open_cover_measure volume B hA htheta
    (fun w ↦ box_volume_ne_zero (dyadicBox B w)) hroot hparent

end OAI.Analysis.PDE.Elliptic
