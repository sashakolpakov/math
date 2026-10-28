import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EquationImage
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.NeighborImages
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius

/-! # Common Pair Images -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairImages.CM

noncomputable section

/-! Recover the original source images and every original reduced
neighbor image from the constructed common pair evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

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
  (c : Fin (M.componentCount a))
  (p : Bool → (Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a c))
  (lc : ∀ b, Witt.PointLift.CM.ComponentLift R hden a c (p b))

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (Witt.ArithmeticBase.CM.Generic.F q) := Witt.EvaluationDVR.CM.fractionCharZero q

variable
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (data : ∀ b, Intrinsic.EvaluationData.CM.Evaluation (L := Witt.ArithmeticBase.CM.Generic.F q)
    (Source.RestrictedPlace.CM.choice M j) (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
    (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) active multiplicative hTorsionQuotient
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b)))

local notation "CF" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.commonField M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable
  (hg : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "source" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.sourcePoint M hM j hsplit R labels hlabels a hden c p lc C
  active multiplicative hTorsionQuotient data
local notation "neighbors" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.neighbors M hM j hsplit R labels hlabels a hden c p lc C
  active multiplicative hTorsionQuotient data hIsogenyQuotient

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM

local notation "alg" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.scalarAlgebra M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "tower" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.scalarTower M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "val" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.valuationDVR M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data
local notation "emb" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairEquation.CM.embedding M hM j hsplit R labels hlabels a hden c p lc
  active multiplicative hTorsionQuotient data

variable {M j} in
def pointImage (point₀ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a) :
    Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Intrinsic.Frobenius.CM.specialAlbanese R a).X) :=
  Additive.ofMul (point₀ ≫ (Over.pullback R.specialBase).map
    (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a)))

def sourceImage (b : Bool) := pointImage R a
  (ReductionPoints.CM.primeFieldPoint R a (Witt.ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p b)))

def reducedImages (b : Bool) (i : Fin 3) :
    Multiset (Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Intrinsic.Frobenius.CM.specialAlbanese R a).X)) :=
  (Intrinsic.EvaluationData.CM.reducedNeighbors (L := Witt.ArithmeticBase.CM.Generic.F q) (Source.RestrictedPlace.CM.choice M j)
    (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) active multiplicative hTorsionQuotient
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b))
    (data b) (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden) i).map (pointImage R a)

theorem source_image (b : Bool) : letI := alg
    letI := tower
    Intrinsic.EquationData.CM.IntrinsicPoints.image HD hgeometry j hden R.residue R.residue_compatibility val (source b) =
      sourceImage M j R a c p b := by
  let := alg
  let := tower
  exact Witt.EquationImage.CM.source_image M hM j hsplit R labels hlabels a hden
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p b))
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b))
    C (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry val

include hg in
theorem neighbor_images (b : Bool) (i : Fin 3) : letI := alg
    letI := tower
    (neighbors b i).map (Intrinsic.EquationData.CM.IntrinsicPoints.image HD hgeometry j hden R.residue R.residue_compatibility val) =
      reducedImages M hM j hsplit R labels hlabels a hden c p lc active multiplicative hTorsionQuotient data b i := by
  let := alg
  let := tower
  let := (data b).field.scalarAlgebra (Witt.ArithmeticBase.CM.W (q := q))
  let := (data b).field.scalarTower (Witt.ArithmeticBase.CM.W (q := q))
  exact Witt.NeighborImages.CM.neighbor_images M hM j hsplit R labels hlabels a hden
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.point M j R a c (p b))
    (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b))
    C active multiplicative hTorsionQuotient (data b).field (data b).valuation (data b).quotient
    val (emb b) hg hgeometry hIsogenyQuotient i

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairImages.CM
