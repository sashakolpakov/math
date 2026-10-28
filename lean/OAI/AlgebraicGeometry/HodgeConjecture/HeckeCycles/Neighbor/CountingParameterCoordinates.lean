import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingKernelParameters
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration

/-! # Counting Parameter Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingParameterCoordinates.CM

noncomputable section

/-! The native parameter coordinates classify chosen kernels on an
arbitrary test scheme. The original evaluated labels therefore still
classify the full parameter set after every further field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (active : Fin s) (multiplicative : Fin s → Bool)
  (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) {x : D.GeometricPoint} (l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b residueIso x)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin s) :
    Module (ZMod (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
    (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents_bound active multiplicative i v)

local instance heckeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v)))

def coordinateEquiv (i : Fin 3) (T : Over (Spec (.of L))) :
    (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborChoiceFunctor (l.genericPolarized (L := L)).abelian q active multiplicative
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) i).obj (.op T) ≃
      Intrinsic.ParameterKernels.CM.Parameters j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l) T
        (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (fun v => labels (.inl v)) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i) :=
  (AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor
    (l.genericPolarized (L := L)).abelian.scheme (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v))
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v)) (.op T)).trans
    (Equiv.piCongrRight fun v => Intrinsic.ParameterBaseChange.CM.supportCongr
      (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).abelian.scheme (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v)) _ _
      (CountingKernelParameters.CM.generic_projector j hsplit l (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v))).symm T)

variable (d : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

variable {L' : Type} [Field L'] (σ : d.carrier →+* L')

def extendedParameterEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    Intrinsic.ParameterKernels.CM.Parameters j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l)
      ((d.family (some i)).extendedParameterBase L' σ)
      (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (fun v => labels (.inl v)) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i) :=
  ((d.family (some i)).extendedChoiceEquiv L' σ
    (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborChoiceFunctor (l.genericPolarized (L := L)).abelian q active multiplicative
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) i)
    (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.nativeNeighborParameter (l.genericPolarized (L := L)).abelian q active multiplicative
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) h_TorsionQuotient i).represents).trans
    (coordinateEquiv j hsplit labels active multiplicative l i _)

def extendedKernelEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    AbelianScheme.TateComparison.Subgroups.KernelChoices ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback ((d.family (some i)).extendedParameterBase L' σ).hom)
      (fun v => j.localCharacter iota (labels (.inl v))) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i) :=
  (extendedParameterEquiv j hsplit labels active multiplicative h_TorsionQuotient l d σ i).trans
    (Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l)
      (𝟙 (Spec (.of L))) ((d.family (some i)).extendedParameterBase L' σ)
      (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (fun v => labels (.inl v)) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingParameterCoordinates.CM
