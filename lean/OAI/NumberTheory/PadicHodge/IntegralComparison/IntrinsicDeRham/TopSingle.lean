import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

/-! # Top Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingle.Intrinsic

noncomputable section

/-! Top differential forms give an actual single-degree coefficient
map into the original sheafified de Rham complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]

abbrev coefficient := (AlgebraSheafScalars.functor R X).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)

theorem outgoing (j : ℕ) (hj : (ComplexShape.up ℕ).Rel g j) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X g).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).d g j = 0 := by
  apply (Smooth.FormDegreeBound.coefficient_sheaf_isZero R X g j ?_).eq_of_tgt
  change g+1 = j at hj
  omega

def sheafMap : (single _ (.up ℕ) g).obj (coefficient R X g) ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X :=
  mkHomFromSingle (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X g).hom (outgoing R X g)

theorem sheafMap_f : (sheafMap R X g).f g =
    (singleObjXSelf (.up ℕ) g (coefficient R X g)).hom ≫
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X g).hom :=
  mkHomFromSingle_f _ _

def presheafMap :
    (single _ (.up ℕ) g).obj ((Affine.HomologyPresheaf.functor R X).obj
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)) ⟶ CechComplex.Intrinsic.presheafComplex R X :=
  (singleMapHomologicalComplex (CechComplex.Intrinsic.presheaves R X) (.up ℕ) g).inv.app (coefficient R X g) ≫
    ((CechComplex.Intrinsic.presheaves R X).mapHomologicalComplex (.up ℕ)).map (sheafMap R X g)

variable {ι : Type u} (U : ι → X.left.Opens)

def bicomplexMap :=
  ((FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapHomologicalComplex
    (.up ℕ)).map (presheafMap R X g)

def totalMap := HomologicalComplex₂.total.map (bicomplexMap R X g U) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingle.Intrinsic
