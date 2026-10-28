import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor

/-! # Pullback Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackCoordinates.BigCrystallinePullbackCoordinates

noncomputable section

/-! # Actual frame functions commute with geometric affine pullback -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) (W A B σ : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A) (a : σ → B)

local notation "bA" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bA
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A B J δ base φ

theorem translation {Q P : C} (f : Q ⟶ P) (i : σ) :
    FrameLifts.BigCrystallineFrameLifts.translation a ((ι).map f) i =
      FrameLifts.BigCrystallineFrameLifts.translation (φ ∘ a) f i := by
  change (show Q.ring from FrameLifts.BigCrystallineFrameLifts.lift p W B σ J δ base a ((ι).obj Q) i) -
      f.ringMap.toRingHom (show P.ring from FrameLifts.BigCrystallineFrameLifts.lift p W B σ J δ base a ((ι).obj P) i) = _
  exact congrArg₂ (fun x y : Q.ring => x - y)
    (PullbackLifts.BigCrystallinePullbackLifts.lift p W A B σ J δ base φ a Q i)
    (congrArg f.ringMap.toRingHom (PullbackLifts.BigCrystallinePullbackLifts.lift p W A B σ J δ base φ a P i))

def pulledMap {Q P : C} (f : Q ⟶ P) :
    DividedPowerAlgebra P.ring (σ →₀ P.ring) →+* DividedPowerAlgebra Q.ring (σ →₀ Q.ring) :=
  (FrameMaps.BigCrystallineFrameMaps.ambientMap a ((ι).map f)).toRingHom

theorem pulledMap_coefficient {Q P : C} (f : Q ⟶ P) (r : P.ring) :
    pulledMap p W A B σ J δ base φ a f (algebraMap P.ring _ r) =
      algebraMap Q.ring _ (f.ringMap.toRingHom r) :=
  FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a ((ι).map f) r

theorem pulledMap_coordinate {Q P : C} (f : Q ⟶ P) (i : σ) :
    pulledMap p W A B σ J δ base φ a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.ring σ 1 i) =
      algebraMap Q.ring (DividedPowerAlgebra Q.ring (σ →₀ Q.ring))
        (FrameLifts.BigCrystallineFrameLifts.translation (φ ∘ a) f i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i := by
  have hc := FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate a ((ι).map f) i
  exact hc.trans (congrArg (fun x : Q.ring => algebraMap Q.ring
    (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) x + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i)
      (translation p W A B σ J δ base φ a f i))

theorem map_eq {Q P : C} (f : Q ⟶ P) : pulledMap p W A B σ J δ base φ a f =
    (FrameMaps.BigCrystallineFrameMaps.ambientMap (φ ∘ a) f).toRingHom := by
  apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate P.ring σ P.ideal P.dividedPowers
    (DividedPowerAlgebra Q.ring (σ →₀ Q.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.ring σ Q.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.ring σ Q.ideal Q.dividedPowers) _ _
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a ((ι).map f))
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD (φ ∘ a) f)
  · intro r
    exact (pulledMap_coefficient p W A B σ J δ base φ a f r).trans
      (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient (φ ∘ a) f r).symm
  · intro i
    exact (pulledMap_coordinate p W A B σ J δ base φ a f i).trans
      (FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate (φ ∘ a) f i).symm

def functionsIso : (ι).op ⋙ FrameFunctor.BigCrystallineFrameFunctor.functions a ≅
    FrameFunctor.BigCrystallineFrameFunctor.functions (φ ∘ a) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro Q P f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact RingHom.congr_fun (map_eq p W A B σ J δ base φ a f.unop) x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackCoordinates.BigCrystallinePullbackCoordinates
