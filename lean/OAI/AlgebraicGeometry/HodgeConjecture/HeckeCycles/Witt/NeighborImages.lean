import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalTargets
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMap

/-! # Neighbor Images -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.NeighborImages.CM.TargetImage

/-! The Albanese image of each actual branch on the common field is the
image of its original NeighborCounting reduced target. Both point identification and
the total Albanese map are derived from the arithmetic geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
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

  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (ArithmeticBase.CM.Generic.F q) := EvaluationDVR.CM.fractionCharZero q

local instance heckeProjectorGroup (i : Fin 3) (v : Fin M.s) :
    IsMonHom (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors (Source.RestrictedPlace.CM.choice M j) M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
      (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian (l.genericAction (L := ArithmeticBase.CM.Generic.F q))
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) i v) :=
  (l.genericAction (L := ArithmeticBase.CM.Generic.F q)).preservesGroup
    ((Source.RestrictedPlace.CM.choice M j).projector M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels (.inl v)))

variable (d : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField (ArithmeticBase.CM.Generic.F q)
  (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian q active multiplicative
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors (Source.RestrictedPlace.CM.choice M j) M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
      (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian (l.genericAction (L := ArithmeticBase.CM.Generic.F q))
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)) hTorsionQuotient))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "sl" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p l
local notation "z" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM.fieldPoint (L := d.carrier) (OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.toOver (M.integral a)) sl
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable [Algebra (ArithmeticBase.CM.W (q := q)) d.carrier] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) d.carrier]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) d.carrier)
  (i : Fin 3) (β : ULift (Fin (d.count (some i))))
  (Q : Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor (Source.RestrictedPlace.CM.choice M j)
    (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
    active multiplicative hTorsionQuotient l d V i β)

variable {L' : Type} [Field L'] [Algebra (ArithmeticBase.CM.Generic.F q) L']
  [Algebra (ArithmeticBase.CM.W (q := q)) L'] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L']
  (V' : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L') (σ : d.carrier →ₐ[ArithmeticBase.CM.Generic.F q] L')

local notation "extTarget" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRTarget.CM.target V V' σ (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) Q.target

variable
  (hg : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.arithmeticAlbanese HD hgeometry
local notation "α" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM.arithmeticMap HD hgeometry
local notation "branch" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
  active multiplicative hTorsionQuotient d σ hIsogenyQuotient i β
local notation "reducedTarget" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget.specialPoint Q.target (OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V
  (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden))

include hg in
theorem target_point :
    Intrinsic.EquationData.CM.IntrinsicPoints.point HD hgeometry j hden R.residue R.residue_compatibility V'
      (((HD).correspondence (typ i)).endpoint branch) = reducedTarget := by
  have hp := CanonicalTargets.CM.target_point_eq M hM j hsplit R labels hlabels a hden p l C
    active multiplicative hTorsionQuotient d V i β Q V' σ hg hgeometry hIsogenyQuotient
  have hq := CanonicalTargets.CM.equationPoint_eq M hM j hsplit R labels hlabels a hden p l
    active multiplicative hTorsionQuotient d V i β Q V' σ (G).2 α
  exact (congrArg (Intrinsic.EquationData.CM.IntrinsicPoints.point HD hgeometry j hden R.residue
    R.residue_compatibility V') hp.symm).trans hq

include hg in
theorem target_image :
    Intrinsic.EquationData.CM.IntrinsicPoints.image HD hgeometry j hden R.residue R.residue_compatibility V'
      (((HD).correspondence (typ i)).endpoint branch) =
    Additive.ofMul (reducedTarget ≫ (Over.pullback R.specialBase).map
      (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a))) := by
  have hp := target_point M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V
    i β Q V' σ hg hgeometry hIsogenyQuotient
  have ha := AlbaneseMap.CM.Hecke.map_eq (M.integral a) (M.components a) (M.decomposition a) C
    (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry
  exact (congrArg (fun point₀ => Additive.ofMul (point₀ ≫ (Over.pullback R.specialBase).map α)) hp).trans
    (congrArg (fun u => Additive.ofMul (reducedTarget ≫ (Over.pullback R.specialBase).map u)) ha)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.NeighborImages.CM.TargetImage

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.NeighborImages.CM

/-! Map every original branch label to its original reduced target in
the total Albanese, retaining the entire multiset and its multiplicities. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

theorem map_images {I S T A : Type} (xs : Multiset I) (f : I → S) (g : I → T)
    (a : S → A) (b : T → A) (h : ∀ i, a (f i) = b (g i)) :
    (xs.map f).map a = (xs.map g).map b := by
  simp only [Multiset.map_map]
  exact Multiset.map_congr rfl (fun i _ => h i)

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

  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (ArithmeticBase.CM.Generic.F q) := EvaluationDVR.CM.fractionCharZero q

local instance heckeProjectorGroup (i : Fin 3) (v : Fin M.s) :
    IsMonHom (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors (Source.RestrictedPlace.CM.choice M j) M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
      (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian (l.genericAction (L := ArithmeticBase.CM.Generic.F q))
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) i v) :=
  (l.genericAction (L := ArithmeticBase.CM.Generic.F q)).preservesGroup
    ((Source.RestrictedPlace.CM.choice M j).projector M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels (.inl v)))

variable (d : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField (ArithmeticBase.CM.Generic.F q)
  (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian q active multiplicative
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors (Source.RestrictedPlace.CM.choice M j) M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
      (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian (l.genericAction (L := ArithmeticBase.CM.Generic.F q))
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)) hTorsionQuotient))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "sl" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p l
local notation "z" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM.fieldPoint (L := d.carrier) (OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.toOver (M.integral a)) sl
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable [Algebra (ArithmeticBase.CM.W (q := q)) d.carrier] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) d.carrier]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) d.carrier)
  (Q : ∀ (i : Fin 3) (β : ULift (Fin (d.count (some i)))), Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor (Source.RestrictedPlace.CM.choice M j)
    (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
    active multiplicative hTorsionQuotient l d V i β)

variable {L' : Type} [Field L'] [Algebra (ArithmeticBase.CM.Generic.F q) L']
  [Algebra (ArithmeticBase.CM.W (q := q)) L'] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L']
  (V' : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L') (σ : d.carrier →ₐ[ArithmeticBase.CM.Generic.F q] L')

variable
  (hg : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

include hg in
theorem neighbor_images (i : Fin 3) :
    (Finset.univ.val.map (fun β => ((HD).correspondence (typ i)).endpoint
      (CanonicalLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
        active multiplicative hTorsionQuotient d σ hIsogenyQuotient i β))).map
          (Intrinsic.EquationData.CM.IntrinsicPoints.image HD hgeometry j hden R.residue R.residue_compatibility V') =
    (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.nativeReducedNeighbors (Source.RestrictedPlace.CM.choice M j)
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
      active multiplicative hTorsionQuotient l d V
      (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden) Q i).map
        (fun point₀ => Additive.ofMul (point₀ ≫ (Over.pullback R.specialBase).map
          (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a)))) := by
  apply map_images (Finset.univ.val : Multiset (ULift (Fin (d.count (some i)))) )
  intro β
  exact TargetImage.target_image M hM j hsplit R labels hlabels a hden p l C
    active multiplicative hTorsionQuotient d V i β (Q i β) V' σ hg hgeometry hIsogenyQuotient

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.NeighborImages.CM

end

end OAI
