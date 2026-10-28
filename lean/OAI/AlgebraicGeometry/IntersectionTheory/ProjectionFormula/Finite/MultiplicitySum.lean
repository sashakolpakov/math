import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FilteredDivisorEuler

/-! # Multiplicity Sum -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

/-! Repeated fixed filtration factors group into a finite weighted
sum using their actual generic lengths in the selected codimension. -/

open scoped Classical

theorem reindex {α : Type*} (k : ℕ) (v : Fin k → α) (P : α → Prop)
    (w : α → ℕ∞) (hcount : ∀ a, P a → w a = (Finset.univ.filter (fun i => v i = a)).card)
    (e : α → ℚ) :
    (∑ i ∈ Finset.univ.filter (fun i => P (v i)), e (v i)) =
    ∑ a ∈ (Finset.univ.image v).filter P, (w a).toNat * e a := by
  let S := Finset.univ.filter (fun i => P (v i))
  let F := (Finset.univ.image v).filter P
  have hmap : ∀ i ∈ S, v i ∈ F := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      (Finset.mem_filter.mp hi).2⟩
  have hs := Finset.sum_fiberwise_of_maps_to' (s := S) (t := F) (g := v) hmap e
  rw [← hs]
  apply Finset.sum_congr rfl
  intro a ha
  have hPa := (Finset.mem_filter.mp ha).2
  have hf : S.filter (fun i => v i = a) = Finset.univ.filter (fun i => v i = a) := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hi
      exact ⟨hi ▸ hPa, hi⟩
  rw [hf, Finset.sum_const, hcount a hPa, ENat.toNat_natCast, nsmul_eq_mul]

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum.LocalCycle

/-! A finite cycle pairing can be reindexed by an injective chart
support list whenever every omitted contribution is zero. -/

open scoped Classical

theorem reindex {α β : Type*} (b : α →₀ ℚ) (e : α → ℚ)
    (T : Finset β) (v : β → α) (hv : Function.Injective v) (w : β → ℚ)
    (hcoeff : ∀ z ∈ T, b (v z) = w z)
    (hout : ∀ A, A ∉ T.image v → b A * e A = 0) :
    b.sum (fun A r => r * e A) = ∑ z ∈ T, w z * e (v z) := by
  have hleft : b.sum (fun A r => r * e A) =
      ∑ A ∈ b.support ∪ T.image v, b A * e A := by
    apply Finset.sum_subset Finset.subset_union_left
    intro A _ hA
    rw [Finsupp.notMem_support_iff.mp hA]
    exact zero_mul _
  have hright : (∑ A ∈ T.image v, b A * e A) =
      ∑ A ∈ b.support ∪ T.image v, b A * e A := by
    apply Finset.sum_subset Finset.subset_union_right
    intro A _ hA
    exact hout A hA
  rw [hleft, ← hright, Finset.sum_image (fun _ _ _ _ h => hv h)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hcoeff z hz]

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum.LocalCycle

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum.Difference

/-! Two finite weighted sums can be combined over their union
when each weight vanishes on the other set outside its own support. -/

open scoped Classical

theorem split {α : Type*} (F G : Finset α) (a b e : α → ℚ)
    (ha : ∀ z ∈ G, z ∉ F → a z = 0) (hb : ∀ z ∈ F, z ∉ G → b z = 0) :
    (∑ z ∈ F ∪ G, (a z - b z) * e z) =
      (∑ z ∈ F, a z * e z) - ∑ z ∈ G, b z * e z := by
  have h₁ : (∑ z ∈ F, a z * e z) = ∑ z ∈ F ∪ G, a z * e z := by
    apply Finset.sum_subset Finset.subset_union_left
    intro z hz hnot
    have hzG : z ∈ G := (Finset.mem_union.mp hz).resolve_left hnot
    rw [ha z hzG hnot, zero_mul]
  have h₂ : (∑ z ∈ G, b z * e z) = ∑ z ∈ F ∪ G, b z * e z := by
    apply Finset.sum_subset Finset.subset_union_right
    intro z hz hnot
    have hzF : z ∈ F := (Finset.mem_union.mp hz).resolve_right hnot
    rw [hb z hzF hnot, zero_mul]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← h₁, ← h₂]

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum.Difference

end

end OAI
