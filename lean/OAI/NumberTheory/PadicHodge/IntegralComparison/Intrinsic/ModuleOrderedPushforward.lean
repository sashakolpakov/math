import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex

/-! # Module Ordered Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleOrderedPushforward

noncomputable section

/-! The original finite-source cohomology isomorphism has the literal
ordered inverse-image coordinate after forgetting the coefficient ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  {ι : Type u} [LinearOrder ι] (U : ι → Y.left.Opens) (q n : ℕ)

abbrev forms := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q
abbrev image := (Scheme.Modules.pushforward f.left).obj (forms R X q)
abbrev cover := IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U

local instance opens_limits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

omit [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsProper Y.hom] [Smooth Y.hom] in
private theorem projection :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Opens.map f.left.base) U (forms R X q).presheaf).inv ≫
      OrderedCech.Projection.map U (image R X Y f q).presheaf ≫
      (OrderedCech.Reindex.iso (Opens.map f.left.base) U (forms R X q).presheaf).hom =
    OrderedCech.Projection.map (cover R X Y f U) (forms R X q).presheaf := by
  have h : (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Opens.map f.left.base) U (forms R X q).presheaf).hom ≫
      OrderedCech.Projection.map (cover R X Y f U) (forms R X q).presheaf =
    OrderedCech.Projection.map U (image R X Y f q).presheaf ≫
      (OrderedCech.Reindex.iso (Opens.map f.left.base) U (forms R X q).presheaf).hom :=
    OrderedCech.Reindex.projection (Opens.map f.left.base) U (forms R X q).presheaf
  rw [← h, Iso.inv_hom_id_assoc]

omit [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsProper Y.hom] [Smooth Y.hom] in
theorem comparison :
    (ModuleTraceHomology.pushforwardIso R X Y f U q n).hom ≫
      (ModuleCech.CohomologyNaturality.forgetHomologyIso R Y U (image R X Y f q) n).hom ≫
      homologyMap (OrderedCech.Projection.map U (image R X Y f q).presheaf) n ≫
      homologyMap (OrderedCech.Reindex.iso (Opens.map f.left.base) U (forms R X q).presheaf).hom n =
    (ModuleCech.CohomologyNaturality.forgetHomologyIso R X (cover R X Y f U) (forms R X q) n).hom ≫
      homologyMap (OrderedCech.Projection.map (cover R X Y f U) (forms R X q).presheaf) n := by
  have hp := congrArg (fun a => homologyMap a n) (projection R X Y f U q)
  simp only [homologyMap_comp] at hp
  simp only [ModuleTraceHomology.pushforwardIso, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleOrderedPushforward
