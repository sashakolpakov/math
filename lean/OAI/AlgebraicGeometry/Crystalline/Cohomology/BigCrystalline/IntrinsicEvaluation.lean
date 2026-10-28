import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Evaluation

/-! # Intrinsic Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicEvaluation.BigCrystallineIntrinsicEvaluation

noncomputable section

/-! # Evaluating the original big frame at actual native lifted coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "W" => WittVector p k
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k
  (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
local notation "A" => Q.thickening.ring
local notation "G" => DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)

def bigCoordinate (i : σ) : G :=
  FrameMaps.BigCrystallineFrameMaps.coordinate (p := p) (J := I) (δ := γ) (base := bX) a
    ((IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B).obj Q) i

theorem raw_coordinate (i : σ) :
    IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv p k B σ a Q (bigCoordinate p k B σ a Q i) =
      CrystallineFrame.Map.CrystallineFrameMap.coordinate a Q i := by
  change IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv p k B σ a Q
      (algebraMap A G (IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a Q i) +
        Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator A σ 1 i) =
    algebraMap A G (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i) +
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator A σ 1 i
  rw [map_add, AlgEquiv.commutes, IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv_coordinate]
  change algebraMap A G (IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a Q i) +
      (algebraMap A G (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i -
        IntrinsicLifts.BigCrystallineIntrinsicLifts.lift p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator A σ 1 i) = _
  rw [map_sub]
  abel

variable (y : σ → Q.thickening.ring)
  (hy : ∀ i, Q.thickening.reduction (y i) = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i))

def map : G →+* A :=
  (CrystallineFrame.Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a (𝟙 Q) y hy).toRingHom.comp
    (IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv p k B σ a Q).toRingHom

theorem coefficient (x : Q.thickening.ring) :
    map p k B σ a Q y hy (algebraMap A G x) = x := by
  let f := CrystallineFrame.Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a (𝟙 Q) y hy
  exact (congrArg f ((IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv p k B σ a Q).commutes x)).trans
    (CrystallineFrame.Evaluation.CrystallineFrameEvaluation.ambientMap_coefficient p k B σ a (𝟙 Q) y hy x)

theorem coordinate (i : σ) : map p k B σ a Q y hy (bigCoordinate p k B σ a Q i) = y i := by
  let f := CrystallineFrame.Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a (𝟙 Q) y hy
  exact (congrArg f (raw_coordinate p k B σ a Q i)).trans
    (CrystallineFrame.Evaluation.CrystallineFrameEvaluation.ambientMap_coordinate p k B σ a (𝟙 Q) y hy i)

theorem isDPMorphism : DividedPowers.IsDPMorphism
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
      (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
    Q.thickening.dividedPowers (map p k B σ a Q y hy) :=
  (CrystallineFrame.Evaluation.CrystallineFrameEvaluation.ambientMap_relativePD p k B σ a (𝟙 Q) y hy).comp _
    (IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv_isDPMorphism p k B σ a Q)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicEvaluation.BigCrystallineIntrinsicEvaluation
