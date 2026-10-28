import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockMap

/-! # Disjoint Projective Blocks -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointProjectiveBlocks

noncomputable section

/-! Two projective spaces embed as disjoint coordinate blocks in
one larger projective space, over the complex base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem disjoint {a b n : ℕ} (j : Fin (a + 1) → Fin (n + 1)) (hj : Function.Injective j)
    (k : Fin (b + 1) → Fin (n + 1)) (hk : Function.Injective k)
    (hd : Disjoint (Set.range j) (Set.range k)) :
    Disjoint (Set.range (CoordinateBlockMap.map j hj)) (Set.range (CoordinateBlockMap.map k hk)) := by
  rw [Set.disjoint_left] at hd ⊢
  rintro _ ⟨p, rfl⟩ ⟨q, he⟩
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen a p
  have hki : j i ∉ Set.range k := fun h => hd (Set.mem_range_self i) h
  have hm := CoordinateBlockMap.outside_mem k hk q (j i) hki
  rw [he] at hm
  exact hi ((CoordinateBlockMap.coordinate_mem j hj p i).mp hm)

def leftIndex (a b : ℕ) (i : Fin (a + 1)) : Fin ((a + b + 1) + 1) := ⟨i.val, by omega⟩

def rightIndex (a b : ℕ) (i : Fin (b + 1)) : Fin ((a + b + 1) + 1) := ⟨a + 1 + i.val, by omega⟩

theorem left_injective (a b : ℕ) : Function.Injective (leftIndex a b) := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin ((a + b + 1) + 1) => x.val) he)

theorem right_injective (a b : ℕ) : Function.Injective (rightIndex a b) := by
  intro i j he
  apply Fin.ext
  have h := congrArg Fin.val he
  change a + 1 + i.val = a + 1 + j.val at h
  omega

theorem indices_disjoint (a b : ℕ) : Disjoint (Set.range (leftIndex a b)) (Set.range (rightIndex a b)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, he⟩
  have h := congrArg Fin.val he
  change a + 1 + j.val = i.val at h
  omega

def left (a b : ℕ) : Foundations.Scheme.ProjectiveSpace.projectiveSpace a ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace (a + b + 1) :=
  CoordinateBlockMap.map (leftIndex a b) (left_injective a b)

def right (a b : ℕ) : Foundations.Scheme.ProjectiveSpace.projectiveSpace b ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace (a + b + 1) :=
  CoordinateBlockMap.map (rightIndex a b) (right_injective a b)

instance (a b : ℕ) : IsClosedImmersion (left a b) := inferInstanceAs
  (IsClosedImmersion (CoordinateBlockMap.map (leftIndex a b) (left_injective a b)))

instance (a b : ℕ) : IsClosedImmersion (right a b) := inferInstanceAs
  (IsClosedImmersion (CoordinateBlockMap.map (rightIndex a b) (right_injective a b)))

theorem left_over (a b : ℕ) : left a b ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (a + b + 1) = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase a :=
  CoordinateBlockMap.over_base _ _

theorem right_over (a b : ℕ) : right a b ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (a + b + 1) = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase b :=
  CoordinateBlockMap.over_base _ _

theorem ranges_disjoint (a b : ℕ) : Disjoint (Set.range (left a b)) (Set.range (right a b)) :=
  disjoint _ (left_injective a b) _ (right_injective a b) (indices_disjoint a b)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointProjectiveBlocks
