import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleDiagonalClassImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.CoefficientMap

/-! # Principal Top Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopSingle

noncomputable section

/-! The genuine top-form inclusion on the actual principal diagram,
with its literal coefficient in the original integral-form coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem composite_apply {C : Type*} [Category C]
    {R : Type*} [CommRing R] {P Q S : C ⥤ ModuleCat R}
    (a : P ⟶ Q) (b : Q ⟶ S) (c : P ⟶ S) (h : a ≫ b = c)
    (r : C) (z : P.obj r) : b.app r (a.app r z) = c.app r z :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h r) z

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (U : X.left.affineOpens) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev sheafCoefficient := (ModelSheafComparison.sourceFunctor p k n X).obj
  (IntrinsicDeRham.TopSingle.Intrinsic.coefficient (Truncated.Witt.Ring p k n) X g)

abbrev coefficient := (PrincipalSheaf.Comparison.restriction p k n X U).obj
  (sheafCoefficient p k n X g)

abbrev diagramFunctor :=
  ModelSheafComparison.sourceFunctor p k n X ⋙
    PrincipalSheaf.Comparison.restriction p k n X U

def map : (single _ (.up ℕ) g).obj (coefficient p k n X U g) ⟶
    FractionClass.Integral.target p k n X U :=
  Single.CoefficientMap.map (diagramFunctor p k n X U)
    (IntrinsicDeRham.TopSingle.Intrinsic.coefficient (Truncated.Witt.Ring p k n) X g) g
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex (Truncated.Witt.Ring p k n) X)
    (IntrinsicDeRham.TopSingle.Intrinsic.sheafMap (Truncated.Witt.Ring p k n) X g)

def coefficientMap : coefficient p k n X U g ⟶
    (FractionClass.Integral.target p k n X U).X g :=
  (PrincipalSheaf.Comparison.restriction p k n X U).map
    ((ModelSheafComparison.sourceFunctor p k n X).map
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso (Truncated.Witt.Ring p k n) X g).hom)

omit [Fintype k] [CharP k p] [Smooth X.hom] [X.left.IsSeparated] in
theorem map_f : (PrincipalTopSingle.map p k n X U g).f g =
    (singleObjXSelf (.up ℕ) g (coefficient p k n X U g)).hom ≫ coefficientMap p k n X U g :=
  Single.CoefficientMap.self (diagramFunctor p k n X U)
    (IntrinsicDeRham.TopSingle.Intrinsic.coefficient (Truncated.Witt.Ring p k n) X g) g
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex (Truncated.Witt.Ring p k n) X)
    (IntrinsicDeRham.TopSingle.Intrinsic.sheafMap (Truncated.Witt.Ring p k n) X g)
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso (Truncated.Witt.Ring p k n) X g).hom
    (IntrinsicDeRham.TopSingle.Intrinsic.sheafMap_f (Truncated.Witt.Ring p k n) X g)

omit [Fintype k] [CharP k p] [Smooth X.hom] [X.left.IsSeparated] in
theorem inverse_map_f :
    (singleObjXSelf (.up ℕ) g (coefficient p k n X U g)).inv ≫
      (PrincipalTopSingle.map p k n X U g).f g = coefficientMap p k n X U g :=
  Single.CoefficientMap.inverse_self (diagramFunctor p k n X U)
    (IntrinsicDeRham.TopSingle.Intrinsic.coefficient (Truncated.Witt.Ring p k n) X g) g
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex (Truncated.Witt.Ring p k n) X)
    (IntrinsicDeRham.TopSingle.Intrinsic.sheafMap (Truncated.Witt.Ring p k n) X g)
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.coefficientSheafIso (Truncated.Witt.Ring p k n) X g).hom
    (IntrinsicDeRham.TopSingle.Intrinsic.sheafMap_f (Truncated.Witt.Ring p k n) X g)

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem coefficientMap_apply (r : PrincipalFrame.Index X.left U)
    (x : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g,
      (Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U).obj r)) :
    (coefficientMap p k n X U g).app (op r) (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    ULift.up.{2,1} (ULift.up.{1,0}
      ((Integral.IntrinsicFormNormalization.Intrinsic.iso (Truncated.Witt.Ring p k n) X
        ((Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U).obj r) g).hom x)) := rfl

omit [Fintype k] [CharP k p] [Smooth X.hom] [X.left.IsSeparated] in
theorem component (r : PrincipalFrame.Index X.left U)
    (x : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g,
      (Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U).obj r)) :
    ((PrincipalTopSingle.map p k n X U g).f g).app (op r)
      ((singleObjXSelf (.up ℕ) g (coefficient p k n X U g)).inv.app (op r)
        (ULift.up.{2,1} (ULift.up.{1,0} x))) =
    ULift.up.{2,1} (ULift.up.{1,0}
      ((Integral.IntrinsicFormNormalization.Intrinsic.iso (Truncated.Witt.Ring p k n) X
        ((Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U).obj r) g).hom x)) := by
  exact (composite_apply
    (singleObjXSelf (.up ℕ) g (coefficient p k n X U g)).inv
    ((PrincipalTopSingle.map p k n X U g).f g) (coefficientMap p k n X U g)
    (inverse_map_f p k n X U g) (op r)
    (ULift.up.{2,1} (ULift.up.{1,0} x))).trans (coefficientMap_apply p k n X U g r x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopSingle
