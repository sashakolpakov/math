import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientTransformations

/-! # Section Coefficient Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionCoefficientValues

noncomputable section

/-! In any actual frame, coefficient combinations of sections have the
expected linear combinations of regular-function coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u v
variable {X : Scheme.{u}} {M : X.Modules}

def frameSectionValueAddHom (a : Line.Bundles.structureModule X ⟶ M) [IsIso a] :
    (Line.Bundles.structureModule X ⟶ M) →+ Γ(X, ⊤) where
  toFun s := Frame.Coordinates.frameCoordinate a s
  map_zero' := by simp only [Frame.Coordinates.frameCoordinate, Frame.Coordinates.frameCoordinateEnd, CategoryTheory.Limits.zero_comp, map_zero]
  map_add' s t := by simp only [Frame.Coordinates.frameCoordinate, Frame.Coordinates.frameCoordinateEnd, Preadditive.add_comp, map_add]

theorem frameCoordinate_scalarSection (a s : Line.Bundles.structureModule X ⟶ M) [IsIso a]
    (r : Γ(X, ⊤)) : Frame.Coordinates.frameCoordinate a (Scalar.SectionValues.scalarSection r s) = r * Frame.Coordinates.frameCoordinate a s := by
  have h : (Scalar.SectionValues.scalarSection r s) ≫ inv a = Scalar.SectionValues.scalarSection r (s ≫ inv a) := Category.assoc _ _ _
  exact (congrArg (Frame.Coordinates.structureModuleEndValue X) h).trans (Scalar.SectionValues.scalarSection_globalValue r (s ≫ inv a))

theorem frameCoordinate_coefficientCombination {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (a : Line.Bundles.structureModule X ⟶ M) [IsIso a]
    {ι : Type v} (s : ι → (Line.Bundles.structureModule X ⟶ M)) (v : ι →₀ R) :
    Frame.Coordinates.frameCoordinate a (Section.CoefficientTransformations.coefficientSectionCombination c M s v) =
      ∑ i ∈ v.support, c (v i) * Frame.Coordinates.frameCoordinate a (s i) := by
  rw [Section.CoefficientTransformations.coefficientSectionCombination_sum]
  change frameSectionValueAddHom a (∑ i ∈ v.support, Scalar.SectionValues.scalarSection (c (v i)) (s i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact frameCoordinate_scalarSection a (s i) (c (v i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionCoefficientValues
