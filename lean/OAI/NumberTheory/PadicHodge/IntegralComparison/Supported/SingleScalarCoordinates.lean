import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleOpenCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopCoefficientIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientNaturality

/-! # Single Scalar Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleScalarCoordinates

noncomputable section

/-! Scalar forgetting in the original supported single complex has
the same unshifted coefficient coordinate as its top-class map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type} [Preorder C] [HasFiniteProducts C]
  {ι : Type} [LinearOrder ι] (W : ι → C)
  (A : Type) [CommRing A] (P : Cᵒᵖ ⥤ ModuleCat.{0} A) (c m : ℕ)

abbrev forgetScalars : ModuleCat.{0} A ⥤ AddCommGrpCat := forget₂ _ _
abbrev forgetDiagrams : (Cᵒᵖ ⥤ ModuleCat.{0} A) ⥤ Cᵒᵖ ⥤ AddCommGrpCat :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{0} A) AddCommGrpCat).obj (forgetScalars A)

local instance : HasFiniteBiproducts (ModuleCat.{0} A) := Abelian.hasFiniteBiproducts

theorem forget_coordinates :
    (SingleCoefficientCoordinates.forgetIso W A P c (m+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
        (P ⋙ forgetScalars A) c m).hom =
    (forgetScalars A).map (IntegralComparison.Functor.SingleTotal.homologyIso
      (AugmentedOrdered.CechFunctor.functor W) P c m).hom ≫
      (AugmentedCech.TopClassCoefficients.homologyIso W (forgetScalars A) P m).hom := by
  have hm := IntegralComparison.Functor.MappedSingleCoordinates.comparison (forgetDiagrams (C := C) A)
    (AugmentedOrdered.CechFunctor.functor W) P c m
  have hc := AugmentedCech.SingleCoefficientCoordinates.comparison W (𝟭 (Cᵒᵖ ⥤ ModuleCat.{0} A))
    (forgetScalars A) P c m
  dsimp only [SingleCoefficientCoordinates.forgetIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc]
  erw [hm]
  exact hc

variable {Y : Scheme.{0}} (F : C ⥤ Y.Opens) (N : Y.Modules)
  (e : P ⋙ forgetScalars A ≅ F.op ⋙ SingleOpenCoordinates.sections N)

theorem comparison :
    (SingleCoefficientCoordinates.iso W A F N P e c (m+c)).hom ≫
      (SingleOpenCoordinates.coordinates W F N c m).hom =
    (forgetScalars A).map (IntegralComparison.Functor.SingleTotal.homologyIso
      (AugmentedOrdered.CechFunctor.functor W) P c m).hom ≫
      (AugmentedCech.TopClassCoefficients.homologyIso W (forgetScalars A) P m).hom ≫
      homologyMap (AugmentedOrdered.CechFunctor.complexMap W e.hom) m := by
  have hn := IntegralComparison.Functor.SingleCoefficientNaturality.homology_naturality
    (AugmentedOrdered.CechFunctor.functor W) e.hom c m
  dsimp only [SingleCoefficientCoordinates.iso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [SingleOpenCoordinates.source_coordinates]
  erw [IntegralComparison.Functor.SingleCoefficientNaturality.homology_naturality
      (AugmentedOrdered.CechFunctor.functor W) e.hom c m]
  rw [← Category.assoc, forget_coordinates, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleScalarCoordinates
