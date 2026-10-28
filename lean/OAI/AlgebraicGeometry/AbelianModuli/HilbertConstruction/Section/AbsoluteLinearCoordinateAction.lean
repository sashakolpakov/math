import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LinearSectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveChartCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismOpenFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus

/-! # Absolute Linear Coordinate Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteLinearCoordinateAction

noncomputable section

/-! The actual projective automorphism induced by an invertible
coefficient map takes a section-defined morphism to the morphism defined
by the inverse transformation of its coordinate sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (e : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
variable (ht : ∀ x : X, ∃ i,
  x ∈ Ample.LineBundles.sectionNonvanishing (CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap i))

theorem sectionAbsoluteMorphism_linearCoordinateIso :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism f (CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap) ht := by
  let t := CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap
  let V (ij : Fin (n + 1) × Fin (n + 1)) : X.Opens :=
    Ample.LineBundles.sectionNonvanishing (s ij.1) ⊓ Ample.LineBundles.sectionNonvanishing (t ij.2)
  let C : Scheme.OpenCover.{0} X := {
    I₀ := Fin (n + 1) × Fin (n + 1)
    X ij := (V ij).toScheme
    f ij := (V ij).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, inferInstance⟩
      obtain ⟨i, hi⟩ := hs x
      obtain ⟨j, hj⟩ := ht x
      exact ⟨(i, j), ⟨⟨x, hi, hj⟩, rfl⟩⟩ }
  apply C.hom_ext
  rintro ⟨i, j⟩
  let U := V (i, j)
  have : IsIso (Ample.LineBundles.pullbackSection U.ι (s i)) :=
    PowerLocus.pullbackSection_isIso_of_le (show U ≤ Ample.LineBundles.sectionNonvanishing (s i) from inf_le_left) (s i)
  have : IsIso (Ample.LineBundles.pullbackSection U.ι (t j)) :=
    PowerLocus.pullbackSection_isIso_of_le (show U ≤ Ample.LineBundles.sectionNonvanishing (t j) from inf_le_right) (t j)
  let c := (U.ι ≫ f).appTop.hom
  let v := fun k => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (s i)) (Ample.LineBundles.pullbackSection U.ι (s k))
  let w := GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v
  have hw (k : Fin (n + 1)) :
      Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (s i)) (Ample.LineBundles.pullbackSection U.ι (t k)) = w k :=
    Local.LinearSectionCoordinates.transformedSection_frameCoordinate U.ι f.appTop.hom s e.symm.toLinearMap i k
  have hu := Frame.Coordinates.frameCoordinate_isUnit (Ample.LineBundles.pullbackSection U.ι (s i)) (Ample.LineBundles.pullbackSection U.ι (t j))
  let a : Γ(U.toScheme, ⊤)ˣ := hu.unit
  have ha : Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (s i)) (Ample.LineBundles.pullbackSection U.ι (t j)) = a := hu.unit_spec.symm
  have hj : w j = a := (hw j).symm.trans ha
  have hnorm : (fun k => (↑a⁻¹ : Γ(U.toScheme, ⊤)) * w k) =
      fun k => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (t j)) (Ample.LineBundles.pullbackSection U.ι (t k)) := by
    funext k
    rw [← hw k, Frame.Coordinates.frameCoordinate_change (Ample.LineBundles.pullbackSection U.ι (s i))
      (Ample.LineBundles.pullbackSection U.ι (t j)) (Ample.LineBundles.pullbackSection U.ι (t k)), ha, ← mul_assoc, a.inv_mul, one_mul]
  change U.ι ≫ (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left) =
    U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f t ht
  rw [← Category.assoc, MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame f s hs U i]
  exact (Linear.ProjectiveChartCoordinateChange.projectiveChartMap_linearCoordinates e c v i j
    (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection U.ι (s i))) a hj).trans
      ((Framed.ProjectiveMaps.projectiveChartMap_congr c hnorm j _ (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection U.ι (t j)))).trans
        (MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame f t ht U j).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteLinearCoordinateAction
