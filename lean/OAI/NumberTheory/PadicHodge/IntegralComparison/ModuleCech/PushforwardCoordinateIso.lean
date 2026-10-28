import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardOrderedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality

/-! # Pushforward Coordinate Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardCoordinateIso

noncomputable section

/-! The original module pushforward square in the named native
forgetful cohomology coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  (M : X.left.Modules) {ι : Type u} [LinearOrder ι] (U : ι → Y.left.Opens) (g : ℕ)

local instance opens_limits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

theorem comparison :
    (Pushforward.Comparison.cohomologyIso R X Y f M U g).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso Y.hom U
        ((Scheme.Modules.pushforward f.left).obj M) g).hom =
    (CohomologyNaturality.forgetHomologyIso R X (fun j => f.left ⁻¹ᵁ U j) M g).hom ≫
      homologyMap (OrderedCech.Projection.map (fun j => f.left ⁻¹ᵁ U j) M.presheaf) g ≫
      homologyMap (OrderedCech.Reindex.iso (Opens.map f.left.base) U M.presheaf).inv g := by
  simpa only [CohomologyNaturality.forgetHomologyIso, Iso.trans_hom,
    Iso.symm_hom, homologyMapIso_hom, Category.assoc] using
    PushforwardOrderedCoordinates.comparison R X Y f M U g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardCoordinateIso
