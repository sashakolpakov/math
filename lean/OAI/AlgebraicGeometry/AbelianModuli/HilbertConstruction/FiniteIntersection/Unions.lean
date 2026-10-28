import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Arrows

/-! # Unions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Unions

noncomputable section

/-! Singletons and unions describe the cover and the pairwise intersections in the finite diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

def finiteIntersectionSingleton (i : Finite.AffineIntersections.finiteAffineCoverIndex X) : Finite.AffineIntersections.finiteIntersectionIndex X :=
  ⟨{i}, Finset.singleton_nonempty i⟩

theorem finiteIntersectionOpen_singleton (i : Finite.AffineIntersections.finiteAffineCoverIndex X) :
    Finite.AffineIntersections.finiteIntersectionOpen X (finiteIntersectionSingleton X i) = Finite.AffineIntersections.finiteAffineChartOpen X i := by
  classical
  simp [Finite.AffineIntersections.finiteIntersectionOpen, finiteIntersectionSingleton]

def finiteIntersectionUnion (S T : Finite.AffineIntersections.finiteIntersectionIndex X) : Finite.AffineIntersections.finiteIntersectionIndex X := by
  classical
  exact ⟨S.val ∪ T.val, S.property.mono Finset.subset_union_left⟩

theorem finiteIntersection_subset_union_left (S T : Finite.AffineIntersections.finiteIntersectionIndex X) :
    S.val ⊆ (finiteIntersectionUnion X S T).val := by
  classical
  exact Finset.subset_union_left

theorem finiteIntersection_subset_union_right (S T : Finite.AffineIntersections.finiteIntersectionIndex X) :
    T.val ⊆ (finiteIntersectionUnion X S T).val := by
  classical
  exact Finset.subset_union_right

theorem finiteIntersectionUnion_comm (S T : Finite.AffineIntersections.finiteIntersectionIndex X) :
    finiteIntersectionUnion X S T = finiteIntersectionUnion X T S := by
  classical
  apply Subtype.ext
  exact Finset.union_comm _ _

theorem finiteIntersectionUnion_assoc (S T U : Finite.AffineIntersections.finiteIntersectionIndex X) :
    finiteIntersectionUnion X (finiteIntersectionUnion X S T) U =
      finiteIntersectionUnion X S (finiteIntersectionUnion X T U) := by
  classical
  apply Subtype.ext
  exact Finset.union_assoc _ _ _

theorem finiteIntersectionUnion_self (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    finiteIntersectionUnion X S S = S := by
  classical
  apply Subtype.ext
  exact Finset.union_self _

theorem finiteIntersectionOpen_union (S T : Finite.AffineIntersections.finiteIntersectionIndex X) :
    Finite.AffineIntersections.finiteIntersectionOpen X (finiteIntersectionUnion X S T) =
      Finite.AffineIntersections.finiteIntersectionOpen X S ⊓ Finite.AffineIntersections.finiteIntersectionOpen X T := by
  classical
  apply le_antisymm
  · exact le_inf (Arrows.finiteIntersectionOpen_antitone X Finset.subset_union_left)
      (Arrows.finiteIntersectionOpen_antitone X Finset.subset_union_right)
  · apply le_iInf
    intro i
    obtain hi | hi := Finset.mem_union.mp i.property
    · exact (inf_le_left : Finite.AffineIntersections.finiteIntersectionOpen X S ⊓ Finite.AffineIntersections.finiteIntersectionOpen X T ≤
        Finite.AffineIntersections.finiteIntersectionOpen X S).trans
        (iInf_le (fun k : S.val => Finite.AffineIntersections.finiteAffineChartOpen X k.val) ⟨i.val, hi⟩)
    · exact (inf_le_right : Finite.AffineIntersections.finiteIntersectionOpen X S ⊓ Finite.AffineIntersections.finiteIntersectionOpen X T ≤
        Finite.AffineIntersections.finiteIntersectionOpen X T).trans
        (iInf_le (fun k : T.val => Finite.AffineIntersections.finiteAffineChartOpen X k.val) ⟨i.val, hi⟩)

theorem finiteIntersectionOpen_cover (x : X.left) :
    ∃ S, x ∈ Finite.AffineIntersections.finiteIntersectionOpen X S := by
  obtain ⟨i, hi⟩ := Finite.AffineIntersections.finiteAffineChartOpen_cover X x
  exact ⟨finiteIntersectionSingleton X i, (finiteIntersectionOpen_singleton X i).symm ▸ hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Unions
