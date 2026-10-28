import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentAmbient
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorTo
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Laurent Sectors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.LaurentSectors.Dolbeault

noncomputable section

/-! A finite Laurent sign decomposition with preservation of prescribed zeros. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_finiteLaurentSectors (s Z : Finset ι) (hZ : Disjoint s Z)
    (f : (ι → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s))
    (hz : ∀ j ∈ Z, ∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, x j = 0 → f x = 0) :
    ∃ A : Finset ι → (ι → ℂ) → ℂ,
      (∀ J ∈ s.powerset, Differentiable ℂ (A J) ∧
        ∀ j ∈ J ∪ Z, ∀ x : ι → ℂ, x j = 0 → A J x = 0) ∧
      (∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s,
        ∑ J ∈ s.powerset, A J (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x) = f x) := by
  induction s using Finset.induction_on generalizing Z f with
  | empty =>
    have hall (x : ι → ℂ) : x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (∅ : Finset ι) := by
      rw [Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_empty]
      trivial
    have hdiff : Differentiable ℂ f := by
      apply differentiableOn_univ.mp
      simpa only [Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_empty, Opens.coe_top] using hf
    refine ⟨fun _ => f, ?_, ?_⟩
    · intro J hJ
      have hJe : J = ∅ := by simpa using hJ
      subst J
      refine ⟨hdiff, ?_⟩
      intro j hj x hx
      exact hz j (by simpa using hj) x (hall x) hx
    · intro x _
      have hinv : Laurent.SectorTo.Dolbeault.laurentInverseCoordinates (∅ : Finset ι) x = x := by
        funext i
        simp [Laurent.SectorTo.Dolbeault.laurentInverseCoordinates]
      simp only [Finset.powerset_empty, Finset.sum_singleton, hinv]
  | @insert i s hi ih =>
    have hiZ : i ∉ Z := (Finset.disjoint_insert_left.mp hZ).1
    have hsZ : Disjoint s Z := (Finset.disjoint_insert_left.mp hZ).2
    obtain ⟨a, b, ha, hb, hb0, habz, hab⟩ := Coordinate.LaurentAmbient.Dolbeault.exists_laurentDomain_split s i hi f hf
    have haz : ∀ j ∈ Z, ∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, x j = 0 → a x = 0 := by
      intro j hj x hx hxj
      exact (habz j (fun h => hiZ (h ▸ hj)) (hz j hj) x hx hxj).1
    have hbz : ∀ j ∈ insert i Z, ∀ x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s, x j = 0 → b x = 0 := by
      intro j hj x hx hxj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hb0 x hx hxj
      · exact (habz j (fun h => hiZ (h ▸ hj)) (hz j hj) x hx hxj).2
    obtain ⟨A, hA, hAe⟩ := ih Z hsZ a ha haz
    obtain ⟨B, hB, hBe⟩ := ih (insert i Z) (Finset.disjoint_insert_right.mpr ⟨hi, hsZ⟩) b hb hbz
    let C : Finset ι → (ι → ℂ) → ℂ := fun J => if i ∈ J then B (J.erase i) else A J
    refine ⟨C, ?_, ?_⟩
    · intro J hJ
      have hJs : J ⊆ insert i s := Finset.mem_powerset.mp hJ
      by_cases hiJ : i ∈ J
      · have herase : J.erase i ⊆ s := by
          intro j hj
          rcases Finset.mem_erase.mp hj with ⟨hji, hjJ⟩
          exact (Finset.mem_insert.mp (hJs hjJ)).resolve_left hji
        change Differentiable ℂ (if i ∈ J then B (J.erase i) else A J) ∧ _
        simp only [C, ite_eq_left hiJ]
        refine ⟨(hB _ (Finset.mem_powerset.mpr herase)).1, ?_⟩
        intro j hj x hx
        have hjB : j ∈ J.erase i ∪ insert i Z := by
          by_cases hji : j = i
          · subst j
            exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · rcases Finset.mem_union.mp hj with hj | hj
            · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hji, hj⟩)
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hj)
        exact (hB _ (Finset.mem_powerset.mpr herase)).2 j hjB x hx
      · have hsub : J ⊆ s := by
          intro j hj
          rcases Finset.mem_insert.mp (hJs hj) with hji | hj
          · exact False.elim (hiJ (hji ▸ hj))
          · exact hj
        change Differentiable ℂ (if i ∈ J then B (J.erase i) else A J) ∧ _
        simpa only [C, ite_eq_right hiJ] using hA J (Finset.mem_powerset.mpr hsub)
    · intro x hx
      have hxs : x ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s :=
        Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_antitone (Finset.subset_insert i s) hx
      have hxu : Function.update x i (x i)⁻¹ ∈ Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s :=
        Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_update hi hxs _
      rw [Finset.sum_powerset_insert hi]
      calc
        (∑ J ∈ s.powerset, C J (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x)) +
            ∑ J ∈ s.powerset, C (insert i J) (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates (insert i J) x) =
          (∑ J ∈ s.powerset, A J (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x)) +
            ∑ J ∈ s.powerset, B J (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J (Function.update x i (x i)⁻¹)) := by
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro J hJ
            have hiJ : i ∉ J := fun hj => hi (Finset.mem_powerset.mp hJ hj)
            simp only [C, ite_eq_right hiJ]
          · apply Finset.sum_congr rfl
            intro J hJ
            have hiJ : i ∉ J := fun hj => hi (Finset.mem_powerset.mp hJ hj)
            simp only [C, Finset.mem_insert_self, ite_true, Finset.erase_insert hiJ,
              Laurent.SectorTo.Dolbeault.laurentInverseCoordinates_insert J i hiJ]
        _ = a x + b (Function.update x i (x i)⁻¹) :=
          congrArg₂ (· + ·) (hAe x hxs) (hBe _ hxu)
        _ = f x := hab x hx

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.LaurentSectors.Dolbeault
