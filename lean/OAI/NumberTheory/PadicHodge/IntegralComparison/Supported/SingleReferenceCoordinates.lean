import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientNaturality

/-! # Single Reference Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleReferenceCoordinates.Reference

noncomputable section

/-! The original supported single-module coordinates agree with the
literal additive principal coordinates and preserve the retained coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type} [Preorder C] [HasFiniteProducts C]
  {ι : Type} [LinearOrder ι] (W : ι → C)
  (A : Type) [CommRing A]

abbrev scalarForget : ModuleCat.{0} A ⥤ AddCommGrpCat.{0} := forget₂ _ _
abbrev diagramForget : (Cᵒᵖ ⥤ ModuleCat.{0} A) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Functor.whiskeringRight _ _ _).obj (scalarForget A)

local instance finiteBiproducts : HasFiniteBiproducts (ModuleCat.{0} A) := Abelian.hasFiniteBiproducts

variable (P : Cᵒᵖ ⥤ ModuleCat.{0} A) (c g : ℕ)

abbrev coefficientIso := AugmentedCech.SingleCoefficientCoordinates.coefficientIso W
  (𝟭 (Cᵒᵖ ⥤ ModuleCat.{0} A)) (scalarForget A) P g

theorem forget_coordinates :
    (SingleCoefficientCoordinates.forgetIso W A P c (g+c)).hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
        (P ⋙ scalarForget A) c g).hom =
    (scalarForget A).map (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W) P c g).hom ≫
      (coefficientIso W A P g).hom := by
  have hm := IntegralComparison.Functor.MappedSingleCoordinates.comparison (diagramForget (C := C) A)
    (AugmentedOrdered.CechFunctor.functor W) P c g
  have hc := AugmentedCech.SingleCoefficientCoordinates.comparison W
    (𝟭 (Cᵒᵖ ⥤ ModuleCat.{0} A)) (scalarForget A) P c g
  change ((AugmentedCech.CoefficientTotal.homologyIso W (scalarForget A)
      ((single _ (.up ℕ) c).obj P) (g+c)).hom ≫
      homologyMap (HomologicalComplex₂.total.map
        (IntegralComparison.Functor.MappedSingleCoordinates.map (diagramForget (C := C) A)
          (AugmentedOrdered.CechFunctor.functor W) P c) (.up ℕ)) (g+c)) ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
        ((diagramForget (C := C) A).obj P) c g).hom = _
  rw [Category.assoc, hm]
  exact hc

variable {Y : Scheme.{0}} (F : C ⥤ Y.Opens) (N : Y.Modules)

abbrev sourceCoordinates := IntegralComparison.Functor.SingleTotal.homologyIso
  (AffinePrincipal.Injective.Comparison.coefficients F ⋙ AugmentedOrdered.CechFunctor.functor W)
  (AffinePrincipal.Injective.Comparison.sheaf N) c g

theorem source_coordinates :
    (SingleCoefficientCoordinates.sourceIso W F N c (g+c)).hom ≫
      (sourceCoordinates W c g F N).hom =
    (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
      (F.op ⋙ (AffinePrincipal.Injective.Comparison.sheaf N).obj) c g).hom := by
  have h : (SingleCoefficientCoordinates.sourceIso W F N c (g+c)).inv ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
        (F.op ⋙ (AffinePrincipal.Injective.Comparison.sheaf N).obj) c g).hom =
      (sourceCoordinates W c g F N).hom :=
    IntegralComparison.Functor.MappedSingleCoordinates.comparison (AffinePrincipal.Injective.Comparison.coefficients F)
      (AugmentedOrdered.CechFunctor.functor W) (AffinePrincipal.Injective.Comparison.sheaf N) c g
  rw [← h, Iso.hom_inv_id_assoc]

variable (e : P ⋙ scalarForget A ≅ F.op ⋙ (AffinePrincipal.Injective.Comparison.sheaf N).obj)

theorem coordinates :
    (SingleCoefficientCoordinates.iso W A F N P e c (g+c)).hom ≫
      (sourceCoordinates W c g F N).hom =
    (scalarForget A).map (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W) P c g).hom ≫
      (coefficientIso W A P g).hom ≫ homologyMap ((AugmentedOrdered.CechFunctor.functor W).map e.hom) g := by
  have hn : (SingleCoefficientCoordinates.singleH W AddCommGrpCat c (g+c)).map e.hom ≫
      (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
        (F.op ⋙ (AffinePrincipal.Injective.Comparison.sheaf N).obj) c g).hom =
    (IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor W)
        (P ⋙ scalarForget A) c g).hom ≫
      homologyMap ((AugmentedOrdered.CechFunctor.functor W).map e.hom) g :=
    IntegralComparison.Functor.SingleCoefficientNaturality.homology_naturality
      (AugmentedOrdered.CechFunctor.functor W) e.hom c g
  dsimp only [SingleCoefficientCoordinates.iso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [source_coordinates, hn, ← Category.assoc, forget_coordinates]
  exact Category.assoc _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleReferenceCoordinates.Reference
