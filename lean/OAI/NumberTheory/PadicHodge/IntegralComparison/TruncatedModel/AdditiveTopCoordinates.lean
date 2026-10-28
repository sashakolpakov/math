import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientHomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates

/-! # Additive Top Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopCoordinates

noncomputable section

/-! The original single top-form complex maps to the native top-form
input through its canonical single-complex isomorphism. The genuine
sheaf top map factors through this same isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev originalLinear := ((Affine.HomologyPresheaf.functor
  (Truncated.Witt.Ring p k n) X).mapHomologicalComplex (.up ℕ)).obj
    ((single X.left.Modules (.up ℕ) g).obj
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g))

def linearSingleIso : originalLinear p k n X g ≅
    IntrinsicOrdered.TopSingle.Intrinsic.source (Truncated.Witt.Ring p k n) X g :=
  ((IntrinsicDeRham.CechComplex.Intrinsic.presheaves (Truncated.Witt.Ring p k n) X).mapHomologicalComplex
    (.up ℕ)).mapIso
      ((singleMapHomologicalComplex
        (AlgebraSheafScalars.functor (Truncated.Witt.Ring p k n) X) (.up ℕ) g).app
          (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)) ≪≫
    (singleMapHomologicalComplex
      (IntrinsicDeRham.CechComplex.Intrinsic.presheaves (Truncated.Witt.Ring p k n) X) (.up ℕ) g).app
        (IntrinsicDeRham.TopSingle.Intrinsic.coefficient (Truncated.Witt.Ring p k n) X g)

omit [Fintype k] [CharP k p] [Smooth X.hom] [X.left.IsSeparated] in
theorem linear_factor :
    (linearSingleIso p k n X g).hom ≫
      IntrinsicDeRham.TopSingle.Intrinsic.presheafMap (Truncated.Witt.Ring p k n) X g =
    ((IntrinsicDeRham.CechComplex.Intrinsic.presheaves (Truncated.Witt.Ring p k n) X).mapHomologicalComplex
      (.up ℕ)).map (AdditiveTop.Comparison.sheafTopMap p k n X g) := by
  simp only [linearSingleIso, Iso.trans_hom, Functor.mapIso_hom,
    IntrinsicDeRham.TopSingle.Intrinsic.presheafMap, Iso.app_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
    AdditiveTop.Comparison.sheafTopMap, Functor.map_comp]

abbrev changeFunctor := (Functor.whiskeringRight X.left.Opensᵒᵖ
  (ModuleCat (Truncated.Witt.Ring p k n))
  (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))).obj
    (OrdinarySectionMap.Ordinary.coefficients p k n)

abbrev forgetFunctor := (Functor.whiskeringRight X.left.Opensᵒᵖ
  (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
  AddCommGrpCat.{2}).obj (AdditiveTop.Comparison.forget p k)

def singleIso :
    AugmentedCech.CoefficientTotal.mapped AdditiveTop.Comparison.lift
      (AdditiveTop.Comparison.originalTop p k n X g) ≅
    OrderedCech.CoefficientTotal.mapped (AdditiveTop.Comparison.forget p k)
      (OrderedCech.CoefficientTotal.mapped (OrdinarySectionMap.Ordinary.coefficients p k n)
        (IntrinsicOrdered.TopSingle.Intrinsic.source (Truncated.Witt.Ring p k n) X g)) :=
  ((forgetFunctor p k n X).mapHomologicalComplex (.up ℕ)).mapIso
    (((changeFunctor p k n X).mapHomologicalComplex (.up ℕ)).mapIso
      (linearSingleIso p k n X g))

omit [Fintype k] [CharP k p] [Smooth X.hom] [X.left.IsSeparated] in
theorem topUnit_factor : AdditiveTop.Comparison.topUnit p k n X g =
    (singleIso p k n X g).hom ≫
      OrderedCech.CoefficientNaturality.Total.mappedComplexMap
        (AdditiveTop.Comparison.forget p k)
        (OrderedCech.CoefficientNaturality.Total.mappedComplexMap
          (OrdinarySectionMap.Ordinary.coefficients p k n)
          (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap (Truncated.Witt.Ring p k n) X g)) := by
  have h := congrArg (fun a =>
    ((forgetFunctor p k n X).mapHomologicalComplex (.up ℕ)).map
      (((changeFunctor p k n X).mapHomologicalComplex (.up ℕ)).map a))
    (linear_factor p k n X g)
  simp only [Functor.map_comp] at h
  exact h.symm

abbrev cover := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X

def totalIso := HomologicalComplex₂.total.mapIso
  (((OrderedCech.Functor.Projection.functor (cover p k n X)).mapHomologicalComplex (.up ℕ)).mapIso
    (singleIso p k n X g)) (.up ℕ)

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem total_factor :
    OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
      (AdditiveTop.Comparison.topUnit p k n X g) =
    (totalIso p k n X g).hom ≫
      OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
        (OrderedCech.CoefficientNaturality.Total.mappedComplexMap
          (AdditiveTop.Comparison.forget p k)
          (OrderedCech.CoefficientNaturality.Total.mappedComplexMap
            (OrdinarySectionMap.Ordinary.coefficients p k n)
            (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap (Truncated.Witt.Ring p k n) X g))) := by
  rw [topUnit_factor]
  simp only [OrderedCech.CoefficientNaturality.Total.totalMap, OrderedCech.CoefficientNaturality.Total.bicomplexMap,
    Functor.map_comp, HomologicalComplex₂.total.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopCoordinates
