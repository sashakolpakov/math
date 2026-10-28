import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorPoint

/-! # Positive Projective Ambient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PositiveProjectiveAmbient

noncomputable section

/-! Every actual projective presentation admits a positive-dimensional projective ambient space, including zero-dimensional presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projectiveZeroCoordinate_eq_top : Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 0 0 = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen 0 x
  have h : i = 0 := Fin.ext (by omega)
  exact h ▸ hi

theorem projectiveZeroToBase_isIso : IsIso (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 0) := by
  let : IsEmpty {j : Fin (0 + 1) // j ≠ 0} :=
    ⟨fun j => j.property (Fin.ext (by omega))⟩
  have : IsIso (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 0 0).ι := by
    rw [projectiveZeroCoordinate_eq_top]
    change IsIso (Foundations.Scheme.ProjectiveSpace.projectiveSpace 0).topIso.hom
    infer_instance
  have : IsIso ((Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 0 0).ι ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 0) := by
    rw [← Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoAffineSpace_over 0 0]
    infer_instance
  exact IsIso.of_isIso_comp_left (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 0 0).ι (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 0)

def projectiveLineBasePoint : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 :=
  Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (fun _ : Fin 2 => (1 : ℂ)) (by
    intro h
    exact one_ne_zero (congrFun h 0))

theorem projectiveLineBasePoint_over :
    projectiveLineBasePoint ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase :=
  Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint_over_base _ _

theorem projectiveLineBasePoint_closed : IsClosedImmersion projectiveLineBasePoint := by
  have : IsClosedImmersion (projectiveLineBasePoint ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) := by
    rw [projectiveLineBasePoint_over]
    infer_instance
  exact IsClosedImmersion.of_comp projectiveLineBasePoint (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)

theorem exists_positive_projective_embedding {X : Scheme.{0}} {g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X g) :
    ∃ (n : ℕ) (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace (n + 1)),
      IsClosedImmersion i ∧ i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1) = g := by
  rcases P with ⟨n, i, hi, hg⟩
  cases n with
  | zero =>
    have := projectiveZeroToBase_isIso
    have := projectiveLineBasePoint_closed
    refine ⟨0, i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 0 ≫ projectiveLineBasePoint, inferInstance, ?_⟩
    rw [Category.assoc, Category.assoc, projectiveLineBasePoint_over, Category.comp_id]
    exact hg
  | succ n => exact ⟨n, i, hi, hg⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.PositiveProjectiveAmbient
