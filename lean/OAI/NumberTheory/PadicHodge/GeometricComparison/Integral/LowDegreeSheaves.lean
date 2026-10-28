import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms

/-! # Low Degree Sheaves -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeSheaves.IntegralLowDegreeSheaves

noncomputable section

/-! The first two native de Rham sheaves and their differential agree with functions and Kähler one-forms before inverting the prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

def zeroPresheafIso : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 0 ≅ AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.functionsPresheaf R X :=
  NatIso.ofComponents (fun U =>
    ((ZeroForms.IntegralZeroForms.equiv R ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj U)).restrictScalars R).toModuleIso)
    (by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      exact ZeroForms.IntegralZeroForms.naturality ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map f) ω)

def onePresheafIso : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X 1 ≅ AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsPresheaf R X :=
  NatIso.ofComponents (fun U =>
    ((OneForms.IntegralOneForms.equiv R ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj U)).restrictScalars R).toModuleIso)
    (by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      exact OneForms.IntegralOneForms.naturality ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map f) ω)

theorem first_differential : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X 0 ≫ (onePresheafIso R X).hom =
    (zeroPresheafIso R X).hom ≫ AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.dZero R X := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  obtain ⟨a, rfl⟩ := (ZeroForms.IntegralZeroForms.equiv R ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj U)).symm.surjective ω
  change OneForms.IntegralOneForms.equiv R _ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R _ 0
    ((ZeroForms.IntegralZeroForms.equiv R _).symm a)) =
      KaehlerDifferential.D R _ (ZeroForms.IntegralZeroForms.equiv R _ ((ZeroForms.IntegralZeroForms.equiv R _).symm a))
  rw [LinearEquiv.apply_symm_apply]
  exact ZeroForms.IntegralZeroForms.first_differential R _ a

def zeroSheafIso : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X 0 ≅
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.functionsPresheaf R X) :=
  (presheafToSheaf _ _).mapIso (zeroPresheafIso R X)

def oneSheafIso : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X 1 ≅
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsPresheaf R X) :=
  (presheafToSheaf _ _).mapIso (onePresheafIso R X)

theorem sheaf_first_differential : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).d 0 1 ≫ (oneSheafIso R X).hom =
    (zeroSheafIso R X).hom ≫ AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.dZeroSheaf R X := by
  have h := congrArg (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).map
    (first_differential R X)
  simp only [Functor.map_comp] at h
  convert h using 1
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeSheaves.IntegralLowDegreeSheaves
