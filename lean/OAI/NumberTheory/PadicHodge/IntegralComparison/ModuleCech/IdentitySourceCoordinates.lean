import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardCoordinateIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Source
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdentityPushforwardModule

/-! # Identity Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.IdentitySourceCoordinates

noncomputable section

/-! The original module pushforward coordinates with an identity
first stage retain the actual native source module Cech class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R]
  (X Z : Over (Spec (CommRingCat.of R))) (i : X ⟶ Z)
  (N : X.left.Modules) {ι : Type} [LinearOrder ι] (V : ι → Z.left.Opens) (c g : ℕ)

local instance i_limits : PreservesFiniteLimits (Opens.map i.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass i.left.base.frameHom).toFunctor
  infer_instance

theorem comparison :
    (Pushforward.Comparison.cohomologyIso R X Z i N V g).hom ≫
      PrincipalReference.Source.ReferenceComparison.sourceOutput (𝟙 X.left) i.left Z.hom V N c g =
    (CohomologyNaturality.forgetHomologyIso R X (fun j => i.left ⁻¹ᵁ V j) N g).hom ≫
      homologyMap (OrderedCech.Projection.map (fun j => i.left ⁻¹ᵁ V j) N.presheaf) g ≫
      (PrincipalSource.PushforwardCoordinates.globalCoordinates (𝟙 X.left) i.left V N c g).inv := by
  have h := PushforwardCoordinateIso.comparison R X Z i N V g
  have hh := congrArg (fun a => a ≫
    homologyMap (OrderedCech.Reindex.iso (Opens.map i.left.base) V N.presheaf).hom g) h
  simp only [Category.assoc, ← homologyMap_comp, Iso.inv_hom_id,
    Category.comp_id] at hh
  have out := congrArg (fun a => a ≫
    (PrincipalSource.PushforwardCoordinates.globalCoordinates (𝟙 X.left) i.left V N c g).inv) hh
  simp only [PrincipalReference.Source.ReferenceComparison.sourceOutput,
    PrincipalReference.Source.ReferenceComparison.image, PrincipalSource.OpenRestriction.image,
    IdentityPushforwardModule.object, PrincipalSource.PushforwardCoordinates.outputCoordinates,
    PrincipalSource.PushforwardCoordinates.reindex, RelativeCech.ReindexData.preimage,
    Category.assoc] at out ⊢
  exact out

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.IdentitySourceCoordinates
