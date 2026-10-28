import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Ordinary Section -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly

noncomputable section

/-! Assembling ordinary de Rham complexes of actual open sections gives
the original de Rham presheaf complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

def diagram := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor R

def iso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (diagram R X) ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simp only [Iso.refl_hom]
    apply NatTrans.ext
    funext U
    change ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d i (i + 1)).app U =
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R Γ(X.left, U.unop)).d i (i + 1)
    dsimp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinarySection.OrdinarySectionComplexAssembly
