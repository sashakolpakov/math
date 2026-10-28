import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitProjectiveMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousChartRenaming
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis

/-! # Coordinate Block Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockMap

noncomputable section

/-! Coordinate subspaces as actual closed projective embeddings,
with exact coordinate-ideal membership. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

variable {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j)

def form (k : Fin (n + 1)) : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 :=
  ∑ a : Fin (m + 1), if j a = k then LinearFormBasis.coordinate m a else 0

include hj in
theorem form_image (a : Fin (m + 1)) : form j (j a) = LinearFormBasis.coordinate m a := by
  simp only [form, hj.eq_iff]
  simp

theorem form_outside (k : Fin (n + 1)) (hk : k ∉ Set.range j) : form j k = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact ite_eq_right (fun he => hk ⟨a, he⟩)

def graded : Foundations.Scheme.ProjectiveSpace.projectiveGrading n →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading m :=
  HomogeneousCoordinateMap.ofForms (fun k => (form j k).val) (fun k => (form j k).property)

theorem graded_X (k : Fin (n + 1)) : graded j (MvPolynomial.X k) = (form j k).val :=
  HomogeneousCoordinateMap.ofForms_X _ _ k

theorem graded_C (c : ℂ) : graded j (MvPolynomial.C c) = MvPolynomial.C c :=
  HomogeneousCoordinateMap.ofForms_C _ _ c

include hj in
theorem inverse (p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) : graded j (HomogeneousChartRenaming.gradedRename j p) = p := by
  have he : (graded j).toRingHom.comp (HomogeneousChartRenaming.gradedRename j).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change graded j (MvPolynomial.rename j (MvPolynomial.C c)) = MvPolynomial.C c
      rw [MvPolynomial.rename_C, graded_C]
    · intro a
      change graded j (HomogeneousChartRenaming.gradedRename j (MvPolynomial.X a)) = MvPolynomial.X a
      rw [HomogeneousChartRenaming.gradedRename_X, graded_X, form_image j hj]
      rfl
  exact DFunLike.congr_fun he p

def map : Foundations.Scheme.ProjectiveSpace.projectiveSpace m ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n :=
  SplitProjectiveMap.map (graded j) (HomogeneousChartRenaming.gradedRename j) (inverse j hj)

instance closed : IsClosedImmersion (map j hj) :=
  SplitProjectiveMap.closed (graded j) (HomogeneousChartRenaming.gradedRename j) (inverse j hj) (graded_C j)

theorem over_base : map j hj ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m :=
  SplitProjectiveMap.over_base (graded j) (HomogeneousChartRenaming.gradedRename j) (inverse j hj) (graded_C j)

theorem coordinate_mem (p : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (a : Fin (m + 1)) :
    MvPolynomial.X (j a) ∈ (map j hj p).asHomogeneousIdeal ↔ MvPolynomial.X a ∈ p.asHomogeneousIdeal := by
  change graded j (MvPolynomial.X (j a)) ∈ p.asHomogeneousIdeal ↔ _
  rw [graded_X, form_image j hj]
  rfl

theorem outside_mem (p : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (k : Fin (n + 1)) (hk : k ∉ Set.range j) :
    MvPolynomial.X k ∈ (map j hj p).asHomogeneousIdeal := by
  change graded j (MvPolynomial.X k) ∈ p.asHomogeneousIdeal
  rw [graded_X, form_outside j k hk]
  exact p.asHomogeneousIdeal.zero_mem

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockMap
