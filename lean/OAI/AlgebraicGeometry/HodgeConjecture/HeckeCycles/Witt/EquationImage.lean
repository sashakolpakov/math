import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EquationPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMap

/-! # Equation Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EquationImage.CM

noncomputable section

/-! The source image in the actual specialized TateComparison equation is the
original prime-field point followed by the original total Albanese map.
The point and map identifications are both derived from the constructed
Witt lift and the original component decomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a)
  (l : Isogenies.NeighborCounting.Lifts.IntegralLift (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a)
    (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.arithmeticMap (j := j) hden) (ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p))

variable (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (hg : (PELSource.CM.heckeData M a C χ).HasIntegralModelGeometry)
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L] [Algebra (ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L] (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L)

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C χ
local notation "sl" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p l
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.arithmeticAlbanese HD hg
local notation "α" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM.arithmeticMap HD hg

theorem source_image :
    Intrinsic.EquationData.CM.IntrinsicPoints.image HD hg j hden R.residue R.residue_compatibility V
      (FieldPoint.CM.fieldPoint (L := L) (M.integral a).toOver sl) =
    Additive.ofMul (ReductionPoints.CM.primeFieldPoint R a p ≫ (Over.pullback R.specialBase).map
      (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a))) := by
  let : IsProper (M.integral a).toOver.hom := hg.proper
  have hp : Intrinsic.EquationData.CM.IntrinsicPoints.point HD hg j hden R.residue R.residue_compatibility V
      (FieldPoint.CM.fieldPoint (L := L) (M.integral a).toOver sl) = ReductionPoints.CM.primeFieldPoint R a p :=
    (EquationPoint.CM.equationPoint_recovers_lift R (G).2 (M.integral a).toOver α sl V).trans
      (Intrinsic.PointFrobenius.CM.pointsEquiv_eq_primeFieldPoint R a p)
  have ha := AlbaneseMap.CM.Hecke.map_eq (M.integral a) (M.components a) (M.decomposition a) C χ hg
  exact (congrArg (fun z => Additive.ofMul (z ≫ (Over.pullback R.specialBase).map α)) hp).trans
    (congrArg (fun u => Additive.ofMul (ReductionPoints.CM.primeFieldPoint R a p ≫ (Over.pullback R.specialBase).map u)) ha)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EquationImage.CM
