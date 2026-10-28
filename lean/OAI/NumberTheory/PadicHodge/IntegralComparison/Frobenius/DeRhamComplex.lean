import OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamFrobeniusLinearity
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # De Rham Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamComplex

noncomputable section

/-!
# IntegralComparison: the actual de Rham complex with its Frobenius-twisted coordinate-module action
-/

open _root_.CategoryTheory

universe u

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C]

def forms (n : ℕ) : ModuleCat.{u} C :=
  (ModuleCat.restrictScalars (FiniteField.frobeniusAlgHom k C).toRingHom).obj
    (ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n))

def differential (n : ℕ) : forms k C n ⟶ forms k C (n + 1) :=
  ModuleCat.ofHom (X := forms k C n) (Y := forms k C (n + 1))
    { toFun := fun x => AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential k C n x
      map_add' := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential k C n).map_add
      map_smul' := DeRhamFrobeniusLinearity.differential_frobenius_smul k C n }

theorem differential_square (n : ℕ) : differential k C n ≫ differential k C (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_square k C n ω

def complex : CochainComplex (ModuleCat.{u} C) ℕ :=
  CochainComplex.of (forms k C) (differential k C) (differential_square k C)

theorem base_comp : (FiniteField.frobeniusAlgHom k C).toRingHom.comp (algebraMap k C) = algebraMap k C :=
  RingHom.ext (FiniteField.frobeniusAlgHom k C).commutes

def baseIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k C)).obj (ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n)) ≅
      ModuleCat.of k (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n) :=
  (AddEquiv.toLinearEquiv
    (M := ↑((ModuleCat.restrictScalars (algebraMap k C)).obj (ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n))))
    (M₂ := ↑(ModuleCat.of k (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n)))
    (by rfl) (fun r x => algebraMap_smul C r (show AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n from x))).toModuleIso

def formsIso (n : ℕ) : (ModuleCat.restrictScalars (algebraMap k C)).obj (forms k C n) ≅
    ModuleCat.of k (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n) :=
  (ModuleCat.restrictScalarsComp'App (algebraMap k C) (FiniteField.frobeniusAlgHom k C).toRingHom
    (algebraMap k C) (base_comp k C).symm (ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n))).symm ≪≫ baseIso k C n

def underlyingIso :
    ((ModuleCat.restrictScalars (algebraMap k C)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (complex k C) ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k C :=
  HomologicalComplex.Hom.isoOfComponents (formsIso k C)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      change (formsIso k C i).hom ≫ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k C).d i (i + 1) =
        (ModuleCat.restrictScalars (algebraMap k C)).map ((complex k C).d i (i + 1)) ≫ (formsIso k C (i + 1)).hom
      dsimp only [complex, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      rfl)

def homologyIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k C)).obj ((complex k C).homology n) ≅
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k C).homology n :=
  (((complex k C).sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap k C))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (underlyingIso k C)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamComplex
