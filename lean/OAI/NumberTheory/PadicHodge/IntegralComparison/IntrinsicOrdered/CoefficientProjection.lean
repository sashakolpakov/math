import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleAdditiveCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv

/-! # Coefficient Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CoefficientProjection.Intrinsic

noncomputable section

/-! The original base-linear ordinary-to-ordered projection retains its
literal additive projection under the original coefficient comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (N : X.Modules)

abbrev scalars := CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)

def orderedIso :
    ((scalars (S := S)).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U) ≅
    OrderedCech.Projection.complex U N.presheaf :=
  ((scalars (S := S)).mapHomologicalComplex (.up ℕ)).mapIso
    (CechCoordinates.Intrinsic.iso π U N).symm ≪≫
  OrderedCech.CoefficientChange.complexIso U (scalars (S := S))
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π N)

theorem cochain :
    ((scalars (S := S)).mapHomologicalComplex (.up ℕ)).map
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π N U) ≫ (orderedIso π U N).hom =
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π N U).hom ≫
      OrderedCech.Projection.map U N.presheaf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro (a : OrderedCech.Projection.Index (ι := ι) n)
  change ((scalars (S := S)).map (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π N U n) ≫
      piComparison (scalars (S := S)) _) ≫
        OrderedCech.Projection.projection U N.presheaf n a =
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π N U).hom.f n ≫
      OrderedCech.Projection.mapF U N.presheaf n) ≫
        OrderedCech.Projection.projection U N.presheaf n a
  rw [Category.assoc]
  erw [piComparison_comp_π, ← Functor.map_comp,
    AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF_comp_π]
  rw [Category.assoc, OrderedCech.Projection.mapF_projection]
  exact (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso_component π N U n a.val).symm

theorem coefficient_coordinates (q : ℕ) :
    (SingleAdditiveCoordinates.Intrinsic.coefficientIso π U N q).hom =
      (IntegralComparison.Functor.HomologySquare.iso (scalars (S := S)) (orderedIso π U N) q).hom := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) q).map
      (CechCoordinates.Intrinsic.iso π U N).inv) (scalars (S := S))
  change (scalars (S := S)).map
      (homologyMap (CechCoordinates.Intrinsic.iso π U N).inv q) ≫
      (((OrderedCech.Projection.complex U (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π N)).sc q).mapHomologyIso (scalars (S := S))).inv =
    (((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).sc q).mapHomologyIso (scalars (S := S))).inv ≫
      homologyMap (((scalars (S := S)).mapHomologicalComplex (.up ℕ)).map
        (CechCoordinates.Intrinsic.iso π U N).inv) q at h
  dsimp only [SingleAdditiveCoordinates.Intrinsic.coefficientIso,
    IntegralComparison.Functor.SingleCoefficientIso.coefficientIso, IntegralComparison.Functor.HomologySquare.iso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homologyMapIso_hom]
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc, ← homologyMap_comp]
  rfl

theorem homology (q : ℕ) :
    (scalars (S := S)).map (homologyMap (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π N U) q) ≫
      (SingleAdditiveCoordinates.Intrinsic.coefficientIso π U N q).hom =
    (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π N U).sc q).mapHomologyIso
      (scalars (S := S))).inv ≫
      homologyMap (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π N U).hom q ≫
        homologyMap (OrderedCech.Projection.map U N.presheaf) q := by
  rw [coefficient_coordinates]
  exact IntegralComparison.Functor.HomologySquare.naturality (scalars (S := S))
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered π N U) (OrderedCech.Projection.map U N.presheaf)
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π N U) (orderedIso π U N) (cochain π U N) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CoefficientProjection.Intrinsic
