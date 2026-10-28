import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopSingleEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ProjectionCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientNaturality

/-! # Top Coefficient Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopCoefficientEdge.Intrinsic

noncomputable section

/-! The original signed top-form edge after exact coefficient change,
with the ordinary native target coordinates and projection retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uD vD
variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.left.Opens)

def nativeMap : IntrinsicDeRham.TopEdge.Intrinsic.source R X U g ⟶
    (IntrinsicDeRham.CechComplex.Intrinsic.total R X U).homology (g+g) :=
  ModuleCat.ofHom (IntrinsicDeRham.TopEdge.Intrinsic.map R X U g)

def topCoordinates :=
  homologyMap (OrderedCech.Projection.map U
    (IntrinsicDeRham.TopSingleCoordinates.Intrinsic.module R X g)) g ≫
      (TopSingle.Intrinsic.sourceIso R X g U g).inv

omit [Finite ι] in
theorem native_comparison :
    topCoordinates R X g U ≫ homologyMap (TopSingle.Intrinsic.map R X g U) (g+g) =
      (((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤˣ) : ℤ) •
        (nativeMap R X g U ≫
          homologyMap (TopSingle.Intrinsic.targetProjection R X U) (g+g))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact TopSingleEdge.Intrinsic.map_apply R X g U x

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasProducts.{0} D] [HasCoproducts.{0} D]
  (G : ModuleCat R ⥤ D) [G.Additive] [PreservesLimitsOfSize.{0,0} G] [G.PreservesHomology]

def mappedTopMap := OrderedCech.CoefficientNaturality.Total.totalMap U
  (OrderedCech.CoefficientNaturality.Total.mappedComplexMap G
    (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap R X g))

def sourceCoordinates := G.map (topCoordinates R X g U) ≫
  (OrderedCech.CoefficientTotal.homologyIso U G
    (TopSingle.Intrinsic.source R X g) (g+g)).hom

omit [Finite ι] in
theorem mapped_naturality :
    G.map (homologyMap (TopSingle.Intrinsic.map R X g U) (g+g)) ≫
      (OrderedCech.CoefficientTotal.homologyIso U G
        (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X) (g+g)).hom =
    (OrderedCech.CoefficientTotal.homologyIso U G
      (TopSingle.Intrinsic.source R X g) (g+g)).hom ≫
        homologyMap (mappedTopMap R X g U G) (g+g) :=
  Functor.HomologySquare.naturality G
    (TopSingle.Intrinsic.map R X g U) (mappedTopMap R X g U G)
    (OrderedCech.CoefficientTotal.totalIso U G (TopSingle.Intrinsic.source R X g))
    (OrderedCech.CoefficientTotal.totalIso U G (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X))
    (OrderedCech.CoefficientNaturality.Total.totalIso_naturality U G
      (IntrinsicDeRham.TopSingle.Intrinsic.presheafMap R X g)) (g+g)

theorem comparison :
    sourceCoordinates R X g U G ≫ homologyMap (mappedTopMap R X g U G) (g+g) =
      (((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤˣ) : ℤ) •
        (G.map (nativeMap R X g U) ≫
          (OrderedCech.ProjectionCoefficients.ordinaryHomologyIso U G
            (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X) (g+g)).hom ≫
          homologyMap (OrderedCech.TotalProjection.map U
            (OrderedCech.CoefficientTotal.mapped G
              (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X))) (g+g))) := by
  unfold sourceCoordinates
  rw [Category.assoc, ← mapped_naturality, ← Category.assoc, ← G.map_comp,
    native_comparison, G.map_zsmul, Preadditive.zsmul_comp, G.map_comp, Category.assoc]
  erw [OrderedCech.ProjectionCoefficients.homology_natural U G
    (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex R X) (g+g)]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopCoefficientEdge.Intrinsic
