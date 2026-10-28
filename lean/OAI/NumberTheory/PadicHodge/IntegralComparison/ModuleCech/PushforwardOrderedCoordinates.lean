import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Pushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CoefficientProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex

/-! # Pushforward Ordered Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardOrderedCoordinates

noncomputable section

/-! The existing module Cech pushforward comparison has the literal
ordered inverse-image comparison as its additive coefficient coordinate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem compose {C : Type*} [Category* C]
    {A B C₀ D E F G H : C} (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D)
    (d : D ≅ E) (e : E ≅ F) (f : F ⟶ G) (g : G ⟶ H)
    (h : D ⟶ H) (r : C₀ ⟶ H)
    (he : f ≫ g = e.inv ≫ d.inv ≫ h) (hr : c ≫ h = r) :
    a ≫ b ≫ c ≫ d.hom ≫ e.hom ≫ f ≫ g = a ≫ b ≫ r := by
  rw [he]
  simp only [Iso.hom_inv_id_assoc]
  rw [hr]

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  (M : X.left.Modules) {ι : Type u} [LinearOrder ι] (U : ι → Y.left.Opens)

local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

theorem inverse_projection :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Opens.map f.left.base) U M.presheaf).inv ≫
      OrderedCech.Projection.map U ((Opens.map f.left.base).op ⋙ M.presheaf) =
    OrderedCech.Projection.map (fun j => f.left ⁻¹ᵁ U j) M.presheaf ≫
      (OrderedCech.Reindex.iso (Opens.map f.left.base) U M.presheaf).inv := by
  apply (cancel_mono (OrderedCech.Reindex.iso (Opens.map f.left.base) U M.presheaf).hom).mp
  rw [Category.assoc, ← OrderedCech.Reindex.projection, ← Category.assoc]
  simp only [Iso.inv_hom_id, Category.id_comp, Category.assoc, Category.comp_id]
  rfl

theorem comparison (g : ℕ) :
    (Pushforward.Comparison.cohomologyIso R X Y f M U g).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso Y.hom U
        ((Scheme.Modules.pushforward f.left).obj M) g).hom =
    (((DimensionBound.complex R X M (fun j => f.left ⁻¹ᵁ U j)).sc g).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv ≫
      homologyMap (DimensionBound.forgetIso R X M
        (fun j => f.left ⁻¹ᵁ U j)).hom g ≫
      homologyMap (OrderedCech.Projection.map (fun j => f.left ⁻¹ᵁ U j) M.presheaf) g ≫
      homologyMap (OrderedCech.Reindex.iso (Opens.map f.left.base) U M.presheaf).inv g := by
  have h := IntrinsicOrdered.CoefficientProjection.Intrinsic.homology Y.hom U
    ((Scheme.Modules.pushforward f.left).obj M) g
  have hr := congrArg (fun a => homologyMap a g) (inverse_projection R X Y f M U)
  simp only [homologyMap_comp] at hr
  have hc := compose
    (((DimensionBound.complex R X M (fun j => f.left ⁻¹ᵁ U j)).sc g).mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv
    (homologyMap (DimensionBound.forgetIso R X M
      (fun j => f.left ⁻¹ᵁ U j)).hom g)
    (homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Opens.map f.left.base) U M.presheaf).inv g)
    (homologyMapIso (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso Y.hom
      ((Scheme.Modules.pushforward f.left).obj M) U) g).symm
    (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj M) U).sc g).mapHomologyIso (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))))
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))).map
      (homologyMap (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechComparison.Scheme.Modules.baseCechToOrdered Y.hom
        ((Scheme.Modules.pushforward f.left).obj M) U) g))
    (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso Y.hom U
      ((Scheme.Modules.pushforward f.left).obj M) g).hom
    (homologyMap (OrderedCech.Projection.map U
      ((Scheme.Modules.pushforward f.left).obj M).presheaf) g)
    (homologyMap (OrderedCech.Projection.map (fun j => f.left ⁻¹ᵁ U j) M.presheaf) g ≫
      homologyMap (OrderedCech.Reindex.iso (Opens.map f.left.base) U M.presheaf).inv g)
    h hr
  simpa only [Pushforward.Comparison.cohomologyIso,
    Pushforward.Comparison.complexIso,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, homologyMapIso_hom, homologyMapIso_inv,
    Functor.mapIso_hom, homologyMap_comp, Category.assoc,
    AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso, HomotopyEquiv.toHomologyIso,
    AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv] using hc

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardOrderedCoordinates
