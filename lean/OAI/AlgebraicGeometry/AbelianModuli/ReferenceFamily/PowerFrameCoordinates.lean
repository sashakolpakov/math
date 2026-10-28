import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameTransitions

/-! # Power Frame Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PowerFrameCoordinates

noncomputable section

/-! Coordinates of the actual sheaf tensor powers in induced local frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

variable {X : Scheme.{0}} (M : X.Modules) (n : ℕ)

def powerSheafFrame (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) :
    HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n ≅ HilbertConstruction.Line.Bundles.structureModule X :=
  (HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).mapIso e ≪≫ HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n

theorem powerSheafFrame_apply (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (W : X.Opens)
    (x : Fin n → Γ(M, W)) :
    (powerSheafFrame M n e).hom.app W ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app W x) =
      ∏ i, (show Γ(X, W) from e.hom.app W (x i)) := by
  have h := congrArg (fun β : HilbertConstruction.Tensor.Powers.SheafMultilinearMap M n (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (HilbertConstruction.Line.Bundles.structureModule X) n) =>
    β.app W x) (HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec e.hom n)
  have hu := congrArg (fun β : HilbertConstruction.Tensor.Powers.SheafMultilinearMap (HilbertConstruction.Line.Bundles.structureModule X) n (HilbertConstruction.Line.Bundles.structureModule X) =>
    β.app W (fun i => e.hom.app W (x i))) (HilbertConstruction.TensorPower.Maps.tensorPowerUnitHom_spec X n)
  exact (congrArg (fun z => (HilbertConstruction.TensorPower.Maps.tensorPowerUnitHom X n).app W z) h).trans hu

def powerFrameOnDomain (U : X.Opens) (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n).restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme :=
  (HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι M n).symm ≪≫ powerSheafFrame (M.restrict U.ι) n e

theorem powerFrameOnImage_apply (U : X.Opens) (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (W : U.toScheme.Opens) (x : Fin n → Γ(M, U.ι ''ᵁ W)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnImage (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) U (powerFrameOnDomain M n U e) W
      ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app (U.ι ''ᵁ W) x) =
        ∏ i, DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e W (x i) := by
  have h := congrArg
    (fun β : HilbertConstruction.Tensor.Powers.SheafMultilinearMap (M.restrict U.ι) n (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (M.restrict U.ι) n) =>
      β.app W x) (HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictInv_spec U.ι M n)
  change (powerSheafFrame (M.restrict U.ι) n e).hom.app W
    ((HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictInv U.ι M n).app W ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app (U.ι ''ᵁ W) x)) = _
  exact (congrArg (fun z => (powerSheafFrame (M.restrict U.ι) n e).hom.app W z) h).trans
    (powerSheafFrame_apply (M.restrict U.ι) n e W x)

theorem powerFrame_transport {V W : X.Opens} (h : V = W)
    (a : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V))
    (c : Γ(HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n, V) ≃ₗ[Γ(X, V)] Γ(X, V))
    (hc : ∀ x, c ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app V x) = ∏ i, a (x i))
    (x : Fin n → Γ(M, W)) :
    DivisorClass.Chern.FramesFrame.Construction.transportFrame (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) h c ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app W x) =
      ∏ i, DivisorClass.Chern.FramesFrame.Construction.transportFrame M h a (x i) := by
  subst W
  exact hc x

theorem powerFrameOnOpen_apply (U : X.Opens) (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (V : X.Opens) (hV : V ≤ U) (x : Fin n → Γ(M, V)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnOpen (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) U (powerFrameOnDomain M n U e) V hV
      ((HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).app V x) = ∏ i, DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e V hV (x i) :=
  powerFrame_transport M n (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen U hV)
    (DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e (U.ι ⁻¹ᵁ V))
    (DivisorClass.Chern.FramesFrame.Construction.frameOnImage (HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) U (powerFrameOnDomain M n U e) (U.ι ⁻¹ᵁ V))
    (powerFrameOnImage_apply M n U e (U.ι ⁻¹ᵁ V)) x

theorem frameTransitionUnit_multilinear {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (B : MultilinearMap R (fun _ : Fin n => V) W)
    (e e' : V ≃ₗ[R] R) (c c' : W ≃ₗ[R] R)
    (hc : ∀ x, c (B x) = ∏ i, e (x i)) (hc' : ∀ x, c' (B x) = ∏ i, e' (x i)) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit c c' = DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit e e' ^ n := by
  have hgen : c'.symm 1 = B (fun _ => e'.symm 1) := by
    apply c'.injective
    rw [LinearEquiv.apply_symm_apply, hc']
    simp only [LinearEquiv.apply_symm_apply, Finset.prod_const_one]
  apply Units.ext
  change c (c'.symm 1) = (e (e'.symm 1)) ^ n
  rw [hgen, hc]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PowerFrameCoordinates
