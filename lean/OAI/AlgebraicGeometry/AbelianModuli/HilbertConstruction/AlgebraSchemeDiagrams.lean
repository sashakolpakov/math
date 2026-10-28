import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecPullbackIso
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Algebra Scheme Diagrams -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagrams

noncomputable section

/-! Coordinate algebra diagrams and their transformations give affine scheme diagrams over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable (C : Type u) [CommRing C] {J : Type v} [Category.{w} J]

abbrev algebraSchemeDiagram (A : Jᵒᵖ ⥤ CommAlgCat.{u} C) : J ⥤ Over (Spec (.of C)) :=
  A.rightOp ⋙ algSpec (.of C)

abbrev algebraSchemeDiagramMap {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C} (φ : A ⟶ B) :
    algebraSchemeDiagram C B ⟶ algebraSchemeDiagram C A :=
  Functor.whiskerRight φ.rightOp (algSpec (.of C))

instance algebraSchemeDiagram_affine (A : Jᵒᵖ ⥤ CommAlgCat.{u} C) (i : J) :
    IsAffine ((algebraSchemeDiagram C A).obj i).left :=
  inferInstanceAs (IsAffine (Spec (.of (A.obj (Opposite.op i)))))

instance algebraSchemeDiagram_smooth (A : Jᵒᵖ ⥤ CommAlgCat.{u} C)
    [∀ i, Algebra.Smooth C (A.obj i)] (i : J) :
    Smooth ((algebraSchemeDiagram C A).obj i).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap C (A.obj (Opposite.op i)))))
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr (inferInstanceAs (Algebra.Smooth C (A.obj (Opposite.op i))))

theorem algebraSchemeDiagramMap_pullback_isIso
    (R : Type u) [CommRing R] [Algebra C R]
    {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C} (φ : A ⟶ B)
    (hφ : ∀ i, Function.Bijective ((AlgebraTensorFunctor.algebraTensorFunctor C R).map (φ.app i)).hom) (i : J) :
    IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map
      ((algebraSchemeDiagramMap C φ).app i)) :=
  AlgebraSpecPullbackIso.isIso_algebraSpec_pullback_of_tensor_bijective (φ.app (Opposite.op i)) (hφ (Opposite.op i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagrams
