import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Universal

/-! # Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Evaluation.CrystallineFrameEvaluation

noncomputable section

/-!
# Evaluating the native frame extension at lifted coordinates

A crystalline morphism together with compatible lifted coordinates
extends to a genuine PD morphism out of the free relative frame algebra.
Its total polynomial coordinates map to the specified lifts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  {P Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}
  (f : P ⟶ Q) (y : σ → P.thickening.ring)
  (hy : ∀ i, P.thickening.reduction (y i) = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P (a i))

local notation "W" => WittVector p k
local notation "QR" => Q.thickening.ring
local notation "PR" => P.thickening.ring
local notation "G" => DividedPowerAlgebra QR (σ →₀ QR)

def difference (i : σ) : PR := y i - f.ambientMap (Lifts.CrystallineFrameLifts.lift p k B σ a Q i)

include hy in
theorem difference_mem (i : σ) : difference p k B σ a f y i ∈ RingHom.ker P.thickening.reduction := by
  change P.thickening.reduction (y i - f.ambientMap (Lifts.CrystallineFrameLifts.lift p k B σ a Q i)) = 0
  rw [map_sub, hy, f.reduction_comm, Lifts.CrystallineFrameLifts.reduction_lift,
    Lifts.CrystallineFrameLifts.residual_naturality f, sub_self]

def ambientMap : G →ₐ[W] PR := by
  letI : Algebra QR PR := f.ambientMap.toRingHom.toAlgebra
  letI : IsScalarTower W QR PR := IsScalarTower.of_algebraMap_eq' f.ambientMap.comp_algebraMap.symm
  exact (FreeRelative.Universal.FreeRelativeUniversal.lift QR σ PR (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers
    (difference p k B σ a f y) (difference_mem p k B σ a f y hy)).restrictScalars W

theorem ambientMap_coefficient (t : QR) :
    CrystallineFrameEvaluation.ambientMap p k B σ a f y hy (algebraMap QR G t) = f.ambientMap t := by
  let : Algebra QR PR := f.ambientMap.toRingHom.toAlgebra
  exact (FreeRelative.Universal.FreeRelativeUniversal.lift QR σ PR (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers
    (difference p k B σ a f y) (difference_mem p k B σ a f y hy)).commutes t

theorem ambientMap_generator (i : σ) :
    CrystallineFrameEvaluation.ambientMap p k B σ a f y hy (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ 1 i) = difference p k B σ a f y i := by
  let : Algebra QR PR := f.ambientMap.toRingHom.toAlgebra
  exact FreeRelative.Universal.FreeRelativeUniversal.lift_coordinate QR σ PR (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers
    (difference p k B σ a f y) (difference_mem p k B σ a f y hy) i

theorem ambientMap_relativePD :
    DividedPowers.IsDPMorphism
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers QR σ (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
      P.thickening.dividedPowers (CrystallineFrameEvaluation.ambientMap p k B σ a f y hy).toRingHom := by
  let : Algebra QR PR := f.ambientMap.toRingHom.toAlgebra
  exact FreeRelative.Universal.FreeRelativeUniversal.lift_isDPMorphism QR σ (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    PR (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers f.dp_comp
    (difference p k B σ a f y) (difference_mem p k B σ a f y hy)

theorem ambientMap_isDPMorphism :
    DividedPowers.IsDPMorphism (Map.CrystallineFrameMap.object p k B σ Q).thickening.dividedPowers
      P.thickening.dividedPowers (CrystallineFrameEvaluation.ambientMap p k B σ a f y hy).toRingHom :=
  (ambientMap_relativePD p k B σ a f y hy).comp _
    (PolynomialThickening.CrystallinePolynomialThickening.identity_inverse_isDPMorphism p k Q.residueRing σ Q.thickening)

theorem ambientMap_coordinate (i : σ) :
    CrystallineFrameEvaluation.ambientMap p k B σ a f y hy (Map.CrystallineFrameMap.coordinate a Q i) = y i := by
  change CrystallineFrameEvaluation.ambientMap p k B σ a f y hy
    (algebraMap QR G (Lifts.CrystallineFrameLifts.lift p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ 1 i) = y i
  rw [map_add, ambientMap_coefficient, ambientMap_generator]
  dsimp only [difference]
  abel

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Evaluation.CrystallineFrameEvaluation
