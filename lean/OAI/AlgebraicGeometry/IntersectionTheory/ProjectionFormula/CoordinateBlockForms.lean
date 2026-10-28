import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

/-! # Coordinate Block Forms -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockForms

noncomputable section

/-! Restriction of linear forms to a projective coordinate block is
a surjective linear map; it also composes exactly with a tuple of
projection coordinates at the graded polynomial level. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockMap

variable {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j)

def restrict : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 where
  toFun p := ⟨CoordinateBlockMap.graded j p.val, (CoordinateBlockMap.graded j).map_mem p.property⟩
  map_add' p q := Subtype.ext ((CoordinateBlockMap.graded j).map_add p.val q.val)
  map_smul' c p := by
    apply Subtype.ext
    exact (MvPolynomial.aeval (fun k => (CoordinateBlockMap.form j k).val)).toLinearMap.map_smul c p.val

include hj in
theorem surjective : Function.Surjective (restrict j) := by
  intro p
  refine ⟨⟨HomogeneousChartRenaming.gradedRename j p.val,
    (HomogeneousChartRenaming.gradedRename j).map_mem p.property⟩, ?_⟩
  exact Subtype.ext (CoordinateBlockMap.inverse j hj p.val)

theorem compose {r : ℕ} (L : Fin (r + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    (CoordinateBlockMap.graded j).comp (Projective.ConeSupport.coordinates L) =
      Projective.ConeSupport.coordinates (fun a => restrict j (L a)) := by
  ext p : 1
  have he : (CoordinateBlockMap.graded j).toRingHom.comp (Projective.ConeSupport.coordinates L).toRingHom =
      (Projective.ConeSupport.coordinates (fun a => restrict j (L a))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change CoordinateBlockMap.graded j (HomogeneousCoordinateMap.ofForms _ _ (MvPolynomial.C c)) =
        HomogeneousCoordinateMap.ofForms _ _ (MvPolynomial.C c)
      rw [HomogeneousCoordinateMap.ofForms_C, CoordinateBlockMap.graded_C, HomogeneousCoordinateMap.ofForms_C]
    · intro a
      change CoordinateBlockMap.graded j (HomogeneousCoordinateMap.ofForms _ _ (MvPolynomial.X a)) =
        HomogeneousCoordinateMap.ofForms _ _ (MvPolynomial.X a)
      rw [HomogeneousCoordinateMap.ofForms_X, HomogeneousCoordinateMap.ofForms_X]
      rfl
  exact DFunLike.congr_fun he p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockForms
