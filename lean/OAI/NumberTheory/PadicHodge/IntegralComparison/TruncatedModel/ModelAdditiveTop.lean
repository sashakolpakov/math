import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleCoefficientCoordinates

/-! # Model Additive Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelAdditiveTop

noncomputable section

/-! The original additive single-form coordinates of the literal
native top input, and its image under the genuine top-form unit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopCoordinates
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g
abbrev module := IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module (Truncated.Witt.Ring p k n) X g
abbrev originalFunctor := Relative.AdditiveCechConcentration.presheaves (X := X.left) ⋙
  (Functor.whiskeringRight X.left.Opensᵒᵖ AddCommGrpCat.{0} AddCommGrpCat.{2}).obj
    AdditiveTop.Comparison.lift ⋙ OrderedCech.Functor.Projection.functor (AdditiveTopCoordinates.cover p k n X)
abbrev mappedFunctor := AdditiveTopCoordinates.changeFunctor p k n X ⋙ AdditiveTopCoordinates.forgetFunctor p k n X ⋙
  OrderedCech.Functor.Projection.functor (AdditiveTopCoordinates.cover p k n X)

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom]
  [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
private theorem linear_single : AdditiveTopCoordinates.linearSingleIso p k n X g =
    (singleMapHomologicalComplex (Affine.HomologyPresheaf.functor
      (Truncated.Witt.Ring p k n) X) (.up ℕ) g).app (form p k n X g) := by
  apply Iso.ext
  apply to_single_hom_ext
  simp only [AdditiveTopCoordinates.linearSingleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, comp_f,
    Functor.mapHomologicalComplex_map_f, singleMapHomologicalComplex_hom_app_self,
    Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rfl

def originalIso (q : ℕ) :=
  IntegralComparison.Functor.SingleTotal.homologyIso (originalFunctor p k n X) (form p k n X g) g q

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
private theorem total_single : (AdditiveTopCoordinates.totalIso p k n X g).hom =
    HomologicalComplex₂.total.map
      (IntegralComparison.Functor.MappedSingleCoordinates.map
        (Affine.HomologyPresheaf.functor (Truncated.Witt.Ring p k n) X)
        (mappedFunctor p k n X) (form p k n X g) g) (.up ℕ) := by
  dsimp only [AdditiveTopCoordinates.totalIso, AdditiveTopCoordinates.singleIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [linear_single]
  rfl

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
private theorem single_coordinates (q : ℕ) :
    (homologyMapIso (AdditiveTopCoordinates.totalIso p k n X g) (q+g)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (mappedFunctor p k n X) (module p k n X g) g q).hom =
    (originalIso p k n X g q).hom := by
  change homologyMap (AdditiveTopCoordinates.totalIso p k n X g).hom (q+g) ≫ _ = _
  rw [total_single]
  exact IntegralComparison.Functor.MappedSingleCoordinates.comparison
    (Affine.HomologyPresheaf.functor (Truncated.Witt.Ring p k n) X)
    (mappedFunctor p k n X) (form p k n X g) g q

abbrev nativeSingle := IntrinsicOrdered.TopSingle.Intrinsic.source (Truncated.Witt.Ring p k n) X g
abbrev coefficientSingle := OrderedCech.CoefficientTotal.mapped
  (OrdinarySectionMap.Ordinary.coefficients p k n) (nativeSingle p k n X g)

def sourceMorphism :=
  (AdditiveTop.Comparison.forget p k).map
    (IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
      (AdditiveTopCoordinates.cover p k n X) (OrdinarySectionMap.Ordinary.coefficients p k n)) ≫
    (OrderedCech.CoefficientTotal.homologyIso (AdditiveTopCoordinates.cover p k n X)
      (AdditiveTop.Comparison.forget p k) (coefficientSingle p k n X g) (g+g)).hom ≫
      (homologyMapIso (AdditiveTopCoordinates.totalIso p k n X g) (g+g)).inv

def input (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (AdditiveTopCoordinates.cover p k n X) g) := sourceMorphism p k n X g (ULift.up.{2,1} (ULift.up.{1,0} x))

def coefficientMorphism :=
  (AdditiveTop.Comparison.forget p k).map
    ((OrdinarySectionMap.Ordinary.coefficients p k n).map
      (homologyMap (OrderedCech.Projection.map (AdditiveTopCoordinates.cover p k n X) (module p k n X g)) g) ≫
      (OrderedCech.SingleCoefficientCoordinates.coefficientIso (AdditiveTopCoordinates.cover p k n X)
        (𝟭 (X.left.Opensᵒᵖ ⥤ ModuleCat (Truncated.Witt.Ring p k n)))
        (OrdinarySectionMap.Ordinary.coefficients p k n) (module p k n X g) g).hom) ≫
    (OrderedCech.SingleCoefficientCoordinates.coefficientIso (AdditiveTopCoordinates.cover p k n X)
      (AdditiveTopCoordinates.changeFunctor p k n X) (AdditiveTop.Comparison.forget p k)
      (module p k n X g) g).hom

omit [Fintype k] [CharP k p] [X.left.IsSeparated]
  [SmoothOfRelativeDimension g X.hom] in
private theorem source_coordinates :
    IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
      (AdditiveTopCoordinates.cover p k n X) (OrdinarySectionMap.Ordinary.coefficients p k n) ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso
        (AdditiveTopCoordinates.changeFunctor p k n X ⋙ OrderedCech.Functor.Projection.functor (AdditiveTopCoordinates.cover p k n X))
        (module p k n X g) g g).hom =
    (OrdinarySectionMap.Ordinary.coefficients p k n).map
      (homologyMap (OrderedCech.Projection.map (AdditiveTopCoordinates.cover p k n X) (module p k n X g)) g) ≫
      (OrderedCech.SingleCoefficientCoordinates.coefficientIso (AdditiveTopCoordinates.cover p k n X)
        (𝟭 (X.left.Opensᵒᵖ ⥤ ModuleCat (Truncated.Witt.Ring p k n)))
        (OrdinarySectionMap.Ordinary.coefficients p k n) (module p k n X g) g).hom := by
  have h := OrderedCech.SingleCoefficientCoordinates.comparison (AdditiveTopCoordinates.cover p k n X)
    (𝟭 (X.left.Opensᵒᵖ ⥤ ModuleCat (Truncated.Witt.Ring p k n)))
    (OrdinarySectionMap.Ordinary.coefficients p k n) (module p k n X g) g g
  dsimp only [IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates]
  rw [Category.assoc]
  erw [h]
  erw [← Category.assoc, ← Functor.map_comp]
  simp only [IntrinsicOrdered.TopCoefficientEdge.Intrinsic.topCoordinates, Category.assoc,
    IntrinsicOrdered.TopSingle.Intrinsic.sourceIso,
    Functor.id_comp, module, Iso.inv_hom_id, Category.comp_id]

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
private theorem mapped_coordinates :
    (AdditiveTop.Comparison.forget p k).map
      (IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
        (AdditiveTopCoordinates.cover p k n X) (OrdinarySectionMap.Ordinary.coefficients p k n)) ≫
      (OrderedCech.CoefficientTotal.homologyIso (AdditiveTopCoordinates.cover p k n X)
        (AdditiveTop.Comparison.forget p k) (coefficientSingle p k n X g) (g+g)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (mappedFunctor p k n X) (module p k n X g) g g).hom =
    coefficientMorphism p k n X g := by
  have h := OrderedCech.SingleCoefficientCoordinates.comparison (AdditiveTopCoordinates.cover p k n X)
    (AdditiveTopCoordinates.changeFunctor p k n X) (AdditiveTop.Comparison.forget p k)
    (module p k n X g) g g
  erw [h]
  erw [← Category.assoc, ← Functor.map_comp]
  erw [source_coordinates]
  rfl

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem coordinates :
    sourceMorphism p k n X g ≫ (originalIso p k n X g g).hom =
      coefficientMorphism p k n X g := by
  rw [sourceMorphism, ← single_coordinates p k n X g g]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact mapped_coordinates p k n X g

omit [Fintype k] [CharP k p] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem input_coordinates (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (AdditiveTopCoordinates.cover p k n X) g) :
    (originalIso p k n X g g).hom (input p k n X g x) =
      coefficientMorphism p k n X g (ULift.up.{2,1} (ULift.up.{1,0} x)) :=
  ConcreteCategory.congr_hom (coordinates p k n X g) _

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem topUnit :
    sourceMorphism p k n X g ≫
      homologyMap (OrderedCech.CoefficientNaturality.Total.totalMap (AdditiveTopCoordinates.cover p k n X)
        (AdditiveTop.Comparison.topUnit p k n X g)) (g+g) =
    (AdditiveTop.Comparison.forget p k).map
      (IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
        (AdditiveTopCoordinates.cover p k n X) (OrdinarySectionMap.Ordinary.coefficients p k n) ≫
      homologyMap (TopCoefficient.map p k n X g) (g+g)) ≫
        (OrderedCech.CoefficientTotal.homologyIso (AdditiveTopCoordinates.cover p k n X)
          (AdditiveTop.Comparison.forget p k)
          (OrderedCech.CoefficientTotal.mapped
            (OrdinarySectionMap.Ordinary.coefficients p k n)
            (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex (Truncated.Witt.Ring p k n) X)) (g+g)).hom := by
  have h := OrderedCech.CoefficientHomologyNaturality.Total.homologyIso_naturality (AdditiveTopCoordinates.cover p k n X)
    (AdditiveTop.Comparison.forget p k)
    (OrderedCech.CoefficientNaturality.Total.mappedComplexMap
      (OrdinarySectionMap.Ordinary.coefficients p k n)
      (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap (Truncated.Witt.Ring p k n) X g)) (g+g)
  rw [sourceMorphism, AdditiveTopCoordinates.total_factor, homologyMap_comp]
  change _ ≫ _ ≫ (homologyMapIso (AdditiveTopCoordinates.totalIso p k n X g) (g+g)).inv ≫
    (homologyMapIso (AdditiveTopCoordinates.totalIso p k n X g) (g+g)).hom ≫ _ = _
  simp only [Iso.inv_hom_id_assoc]
  rw [← h, Functor.map_comp, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelAdditiveTop
