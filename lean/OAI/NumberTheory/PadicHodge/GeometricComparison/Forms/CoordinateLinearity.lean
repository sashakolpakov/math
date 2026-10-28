import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Coordinate Linearity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateLinearity.FormsBaseChange

noncomputable section

/-! Pullback of actual forms is linear over the source coordinate algebra after restricting scalars on the target. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

universe u

theorem formMap_smul {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) (n : ℕ) (a : A) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n (a • ω) = f a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  rw [← (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ.map_smul]
  change (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.rawMap f n (a • x)) =
    f a • (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.rawMap f n x)
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.rawMap_smul, map_smul]

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

def coordinateFormMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n where
  toFun := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n
  map_add' := map_add _
  map_smul' a ω := by
    have h := formMap_smul (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n a ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n (a • ω) =
      algebraMap A B a • AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n ω at h
    exact h.trans (IsScalarTower.algebraMap_smul B a _)

theorem coordinateFormMap_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    coordinateFormMap R A B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateLinearity.FormsBaseChange
