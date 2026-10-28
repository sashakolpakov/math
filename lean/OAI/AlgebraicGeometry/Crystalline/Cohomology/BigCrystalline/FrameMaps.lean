import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps

/-! # Frame Maps -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps.BigCrystallineFrameMaps

noncomputable section

/-! # Actual divided-power coordinate maps on the big crystalline site -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)} (a : σ → A)
  {Q P U : FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base}

def ambientMap (f : Q ⟶ P) : (DividedPowerAlgebra P.ring (σ →₀ P.ring)) →ₐ[W]
    (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) := by
  have ht (w : W) := IsScalarTower.algebraMap_apply W Q.ring
    (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) w
  letI : Algebra P.ring Q.ring := f.ringMap.toRingHom.toAlgebra
  let g := Divided.AffineMaps.DividedAffineMaps.map P.ring Q.ring σ
    Q.ideal Q.dividedPowers
    (FrameLifts.BigCrystallineFrameLifts.translation a f) (FrameLifts.BigCrystallineFrameLifts.translation_mem a f)
  refine { __ := g.toRingHom, commutes' := ?_ }
  intro w
  change g (algebraMap W (DividedPowerAlgebra P.ring (σ →₀ P.ring)) w) = _
  rw [IsScalarTower.algebraMap_apply W P.ring _, Divided.AffineMaps.DividedAffineMaps.map_coefficient]
  have hc : algebraMap P.ring Q.ring (algebraMap W P.ring w) =
      algebraMap W Q.ring w := DFunLike.congr_fun f.overBase w
  rw [hc]
  exact (ht w).symm

theorem ambientMap_coefficient (f : Q ⟶ P) (t : P.ring) :
    ambientMap a f (algebraMap P.ring (DividedPowerAlgebra P.ring (σ →₀ P.ring)) t) =
      algebraMap Q.ring (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) (f.ringMap.toRingHom t) := by
  let : Algebra P.ring Q.ring := f.ringMap.toRingHom.toAlgebra
  exact Divided.AffineMaps.DividedAffineMaps.map_coefficient P.ring Q.ring σ
    Q.ideal Q.dividedPowers
    (FrameLifts.BigCrystallineFrameLifts.translation a f) (FrameLifts.BigCrystallineFrameLifts.translation_mem a f) t

theorem ambientMap_coordinate (f : Q ⟶ P) (i : σ) :
    ambientMap a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.ring σ 1 i) =
      algebraMap Q.ring (DividedPowerAlgebra Q.ring (σ →₀ Q.ring))
        (FrameLifts.BigCrystallineFrameLifts.translation a f i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i := by
  let : Algebra P.ring Q.ring := f.ringMap.toRingHom.toAlgebra
  exact Divided.AffineMaps.DividedAffineMaps.map_coordinate P.ring Q.ring σ
    Q.ideal Q.dividedPowers
    (FrameLifts.BigCrystallineFrameLifts.translation a f) (FrameLifts.BigCrystallineFrameLifts.translation_mem a f) i

theorem ambientMap_relativePD (f : Q ⟶ P) :
    DividedPowers.IsDPMorphism
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers P.ring σ
        P.ideal P.dividedPowers)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.ring σ
        Q.ideal Q.dividedPowers)
      (ambientMap a f).toRingHom := by
  let : Algebra P.ring Q.ring := f.ringMap.toRingHom.toAlgebra
  exact Divided.AffineMaps.DividedAffineMaps.map_isDPMorphism P.ring Q.ring σ
    Q.ideal Q.dividedPowers
    (FrameLifts.BigCrystallineFrameLifts.translation a f) (FrameLifts.BigCrystallineFrameLifts.translation_mem a f)
    P.ideal P.dividedPowers f.ringMap.isDPMorphism

def coordinate (Q : FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base) (i : σ) : (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) :=
  algebraMap Q.ring (DividedPowerAlgebra Q.ring (σ →₀ Q.ring))
    (FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i

theorem coordinate_naturality (f : Q ⟶ P) (i : σ) :
    ambientMap a f (coordinate a P i) = coordinate a Q i := by
  rw [coordinate, map_add, ambientMap_coefficient, ambientMap_coordinate, coordinate]
  change algebraMap Q.ring _ (f.ringMap.toRingHom (FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a P i)) +
    (algebraMap Q.ring _ (FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a Q i -
      f.ringMap.toRingHom (FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a P i)) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i) = _
  rw [map_sub, ← add_assoc, ← add_sub_assoc, add_sub_cancel_left]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps.BigCrystallineFrameMaps
