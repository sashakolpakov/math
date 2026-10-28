import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePushforward

/-! # Scheme Ordered Reindex Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeOrderedReindexComposition

noncomputable section

/-! The literal scheme inverse-image coordinates compose on the
original module presheaf and its genuine pushforward. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Y ⟶ Z)
  (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens) (g : ℕ)

local instance f_limits : PreservesFiniteLimits (Opens.map f.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance
local instance i_limits : PreservesFiniteLimits (Opens.map i.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass i.base.frameHom).toFunctor
  infer_instance
local instance comp_limits : PreservesFiniteLimits (Opens.map (f ≫ i).base) := by
  change PreservesFiniteLimits (OrderHom.ofClass (f ≫ i).base.frameHom).toFunctor
  infer_instance

theorem homology :
    homologyMap (OrderedCech.Reindex.iso (Opens.map i.base) U
      ((Scheme.Modules.pushforward f).obj M).presheaf).inv g ≫
    homologyMap (OrderedCech.Reindex.iso (Opens.map (f ≫ i).base) U M.presheaf).hom g =
    homologyMap (OrderedCech.Reindex.iso (Opens.map f.base) (fun j => i ⁻¹ᵁ U j) M.presheaf).hom g :=
  OrderedCech.ReindexComposition.homology (Opens.map i.base) (Opens.map f.base) U M.presheaf g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeOrderedReindexComposition
