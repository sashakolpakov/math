import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Presheaf Evaluation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.PresheafEvaluation.DeRhamPresheafEvaluation

noncomputable section

/-! Evaluation of the actual native de Rham presheaf complex gives the actual de Rham complex of its section algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens)

def complexIso :
    ((((CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    simp only [Functor.mapHomologicalComplex_obj_d, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex,
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex, CochainComplex.of_d]
    rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.PresheafEvaluation.DeRhamPresheafEvaluation
