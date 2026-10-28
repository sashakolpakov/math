import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopOrdered
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelAdditiveTop

/-! # Additive Top Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopGlobal

noncomputable section

/-! The genuine additive top-form comparison sends the original
native top input to its signed bounded crystalline global edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev cover := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X
abbrev forget := AdditiveTop.Comparison.forget p k

def sourceIso (q : ℕ) := OrderedCech.CoefficientTotal.homologyIso (cover p k n X) (forget p k)
  (SheafProduct.OrderedComparison.source p k n X) q

abbrev targetIso (q : ℕ) := AdditiveGlobal.orderedIso p k n X Y f I (cover p k n X) q

theorem deRham_naturality (q : ℕ) :
    (forget p k).map (homologyMap
      (SheafProduct.OrderedComparison.orderedMap p k n X Y f hp I) q) ≫
        (targetIso p k n X Y f I q).hom =
    (sourceIso p k n X q).hom ≫
      homologyMap (OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
        (AdditiveTop.Comparison.deRhamMap p k n X Y f hp I)) q :=
  OrderedCech.CoefficientHomologyNaturality.Total.homologyIso_naturality (cover p k n X) (forget p k)
    (SheafProduct.OrderedComparison.map p k n X Y f hp I) q

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom]

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem topUnit_coordinates :
    ModelAdditiveTop.sourceMorphism p k n X g ≫
      homologyMap (OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
        (AdditiveTop.Comparison.topUnit p k n X g)) (g+g) =
    (forget p k).map
      (IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
        (cover p k n X) (OrdinarySectionMap.Ordinary.coefficients p k n) ≫
        homologyMap (TopCoefficient.map p k n X g) (g+g)) ≫
      (sourceIso p k n X (g+g)).hom :=
  ModelAdditiveTop.topUnit p k n X g

def map := OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
  (AdditiveTop.Comparison.map p k n X Y f hp I g)

theorem factorization : AdditiveTopGlobal.map p k n X Y f hp I g =
    OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
      (AdditiveTop.Comparison.topUnit p k n X g) ≫
    OrderedCech.CoefficientNaturality.Total.totalMap (cover p k n X)
      (AdditiveTop.Comparison.deRhamMap p k n X Y f hp I) := by
  simp only [AdditiveTopGlobal.map, AdditiveTop.Comparison.map,
    OrderedCech.CoefficientNaturality.Total.totalMap, OrderedCech.CoefficientNaturality.Total.bicomplexMap,
    Functor.map_comp, HomologicalComplex₂.total.map_comp]

theorem source_comparison : ModelAdditiveTop.sourceMorphism p k n X g ≫
    homologyMap (AdditiveTopGlobal.map p k n X Y f hp I g) (g+g) =
    (forget p k).map
      (IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
        (cover p k n X) (OrdinarySectionMap.Ordinary.coefficients p k n) ≫
        homologyMap (TopOrdered.Comparison.map p k n X Y f hp I g) (g+g)) ≫
      (targetIso p k n X Y f I (g+g)).hom := by
  rw [factorization, homologyMap_comp, ← Category.assoc,
    topUnit_coordinates p k n X g, Category.assoc,
    ← deRham_naturality p k n X Y f hp I (g+g), ← Category.assoc, ← Functor.map_comp]
  simp only [TopOrdered.Comparison.map, homologyMap_comp, Category.assoc]

theorem comparison (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (cover p k n X) g) :
    homologyMap (AdditiveTopGlobal.map p k n X Y f hp I g) (g+g)
      (ModelAdditiveTop.input p k n X g x) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      AdditiveGlobal.toOrdered p k n X Y f I (cover p k n X) (g+g)
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I (g+g)
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (cover p k n X) g x)) := by
  have h := ConcreteCategory.congr_hom (source_comparison p k n X Y f hp I g)
    (ULift.up.{2,1} (ULift.up.{1,0} x))
  calc
    _ = (targetIso p k n X Y f I (g+g)).hom
        (homologyMap (TopOrdered.Comparison.map p k n X Y f hp I g) (g+g)
          (TopCoefficient.sourceInput p k n X g x)) := h
    _ = (targetIso p k n X Y f I (g+g)).hom
        (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
          CechIso.ResolutionGlobal.toOrdered p k n X Y f I (cover p k n X) (g+g)
            (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I (g+g)
              (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (cover p k n X) g x))) :=
      congrArg (targetIso p k n X Y f I (g+g)).hom
        (TopOrdered.Comparison.comparison p k n X Y f hp I g x)
    _ = _ := by
      change (targetIso p k n X Y f I (g+g)).hom
        (((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤˣ) : ℤ) • _) = _
      exact map_zsmul (targetIso p k n X Y f I (g+g)).hom.hom _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopGlobal
