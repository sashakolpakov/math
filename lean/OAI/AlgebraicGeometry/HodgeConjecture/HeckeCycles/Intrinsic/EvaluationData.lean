import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Counts

/-! # Evaluation Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EvaluationData.CM

noncomputable section

/-! Keep the actual field, DVR, and full PEL quotients output by native
NeighborCounting in one container. No target comparison or count is a data field;
the count identity is proved from the three native reduction equalities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (active : Fin s) (multiplicative : Fin s → Bool)
variable (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) {x : D.GeometricPoint} (l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b residueIso x)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin s) :
    Module (ZMod (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
    (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents_bound active multiplicative i v)

local instance chosenProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v)))

structure Evaluation where
  field : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
    (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) h_TorsionQuotient)
  valuation : letI := field.scalarAlgebra R
    Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR R field.carrier
  quotient : letI := field.scalarAlgebra R
    letI := field.scalarTower R
    ∀ (i : Fin 3) (β : ULift (Fin (field.count (some i)))),
      Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l field valuation i β

def reducedNeighbors (data : Evaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient l)
    (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b residueIso) (i : Fin 3) : Multiset D.GeometricPoint := by
  letI := data.field.scalarAlgebra R
  letI := data.field.scalarTower R
  exact Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.nativeReducedNeighbors j hsplit labels active multiplicative h_TorsionQuotient l
    data.field data.valuation hbase data.quotient i

omit [IsFractionRing R L] in
theorem exists_evaluation (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b residueIso)
    (X Z : D.OrdinaryPoint → D.OrdinaryPoint) (Y : D.OrdinaryPoint → Multiset D.OrdinaryPoint)
    (o : D.OrdinaryPoint) (lo : Isogenies.NeighborCounting.Lifts.IntegralLift D R b residueIso o.val)
    (h : Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit labels active multiplicative h_TorsionQuotient hbase X Y Z o lo) :
    ∃ data : Evaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient lo,
      ∀ i : Fin 3, reducedNeighbors j hsplit labels active multiplicative h_TorsionQuotient lo data hbase i =
        (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i o).map Subtype.val := by
  obtain ⟨d, V, _, Q, h₀, h₁, h₂⟩ := h
  refine ⟨{ field := d, valuation := V, quotient := Q }, ?_⟩
  exact Ordinary.Counts.CM.OrdinaryRaw.rawNeighbors q X Z Y Subtype.val o _ h₀ h₁ h₂

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EvaluationData.CM
