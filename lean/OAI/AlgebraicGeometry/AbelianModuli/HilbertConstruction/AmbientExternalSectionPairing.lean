import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionToOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.BilinearSections

/-! # Ambient External Section Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalSectionPairing

noncomputable section

/-! Pair local sections on the two factors directly on the intersection of their inverse images in a fixed ambient scheme. This construction is natural under simultaneous shrinking of both opens. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y)
variable (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
variable (M : X.Modules) (N : Y.Modules)

def ambientExternalSectionTensorMap (V : X.Opens) (U : Y.Opens) :
    TensorProduct R ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) →ₗ[R]
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp cX)
      (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))).obj
        (op (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)) := by
  let W := a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U
  let cP := a.appTop.hom.comp cX
  let mMap := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen a cX cP rfl M V W inf_le_left
  let nMap := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen b cY cP hc.symm N U W inf_le_right
  exact TensorProduct.lift
    ((Coefficient.BilinearSections.coefficientTensorSectionPairing cP ((Scheme.Modules.pullback a).obj M)
      ((Scheme.Modules.pullback b).obj N) W).flip.compl₁₂ nMap mMap)

theorem ambientExternalSectionTensorMap_tmul (V : X.Opens) (U : Y.Opens)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    ambientExternalSectionTensorMap a b cX cY hc M N V U (n ⊗ₜ[R] m) =
      (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)).app
        (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)
        (((Scheme.Modules.pullback a).obj M).presheaf.map (homOfLE inf_le_left).op
          (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app V m))
        (((Scheme.Modules.pullback b).obj N).presheaf.map (homOfLE inf_le_right).op
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N).app U n)) := by
  change (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)).app
    (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U)
    (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen a cX (a.appTop.hom.comp cX) rfl M V _ inf_le_left m)
    (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen b cY (a.appTop.hom.comp cX) hc.symm N U _ inf_le_right n) = _
  rw [Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen_apply, Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen_apply]

theorem ambientExternalIntersection_mono
    {V V' : X.Opens} {U U' : Y.Opens} (hV : V' ≤ V) (hU : U' ≤ U) :
    a ⁻¹ᵁ V' ⊓ b ⁻¹ᵁ U' ≤ a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U :=
  inf_le_inf (leOfHom ((TopologicalSpace.Opens.map a.base).map (homOfLE hV)))
    (leOfHom ((TopologicalSpace.Opens.map b.base).map (homOfLE hU)))

theorem ambientExternalSectionTensorMap_naturality
    {V V' : X.Opens} {U U' : Y.Opens} (hV : V' ≤ V) (hU : U' ≤ U)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    ambientExternalSectionTensorMap a b cX cY hc M N V' U'
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op n ⊗ₜ[R]
          (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).map (homOfLE hV).op m) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp cX)
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))).map
          (homOfLE (ambientExternalIntersection_mono a b hV hU)).op
            (ambientExternalSectionTensorMap a b cX cY hc M N V U (n ⊗ₜ[R] m)) := by
  let cP := a.appTop.hom.comp cX
  let W := a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U
  let W' := a ⁻¹ᵁ V' ⊓ b ⁻¹ᵁ U'
  let hW : W' ≤ W := ambientExternalIntersection_mono a b hV hU
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj N
  let mMap := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen a cX cP rfl M V W inf_le_left
  let nMap := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen b cY cP hc.symm N U W inf_le_right
  let mMap' := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen a cX cP rfl M V' W' inf_le_left
  let nMap' := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen b cY cP hc.symm N U' W' inf_le_right
  have hm := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen_naturality a cX cP rfl M
    (W := W) (W' := W') inf_le_left inf_le_left hV hW m
  have hn := Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen_naturality b cY cP hc.symm N
    (W := W) (W' := W') inf_le_right inf_le_right hU hW n
  change (Tensor.Bifunctor.tensorBilinear Ma Nb).coefficientApp cP W'
      (mMap' ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).map (homOfLE hV).op m))
      (nMap' ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).map (homOfLE hU).op n)) =
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cP (Tensor.ProductSheaf.tensorModule Ma Nb)).map (homOfLE hW).op
      ((Tensor.Bifunctor.tensorBilinear Ma Nb).coefficientApp cP W (mMap m) (nMap n))
  rw [Bilinear.Sheaves.SheafBilinearMap.coefficientApp_naturality, ← hm, ← hn]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalSectionPairing
