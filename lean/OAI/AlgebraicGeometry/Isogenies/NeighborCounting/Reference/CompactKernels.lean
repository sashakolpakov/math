import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection

/-! # Compact Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CompactKernels

noncomputable section

/-! Every original evaluated compact choice is the entire prescribed block or its identity, derived from the actual lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection.Neighbor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient))

variable (i : Fin 3) (a : ULift (Fin (d.count (some i)))) (v : Fin s)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (w : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i w)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false (O.compact x)) i w)

def originalCompactKernelIdentity :=
  let hg := Intrinsic.ParameterEnumeration.originalNeighborBlockGeometry j hsplit labels l hTorsionQuotient i v.succ
  letI : IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v.succ)).hom := hg.1
  letI : Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v.succ)).hom := hg.2
  let F := ParameterSubspaces.evaluatedTuple q (O.compact x) i (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i)
    (Intrinsic.ChoiceFunctor.nativeChoiceRepresentation (l.genericPolarized (L := L)).abelian q (O.compact x)
      (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient i) (d.family (some i)) a v.succ
  PLift.up (CompactDetection.Neighbor.neighborCompactChoice_eq q (O.compact x) i
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i) v F
    (fun k _ _ b₀ _ => Lifted.BlockCoordinates.liftedNativeBlockCoordinates j hsplit labels O l hTorsionQuotient
      (HeckeExponents.neighborLevel i) v.succ k b₀))

omit [IsFractionRing R L] in
theorem originalCompactKernel_eq :
    type_of% (originalCompactKernelIdentity j hsplit labels O l hTorsionQuotient d i a v).down :=
  (originalCompactKernelIdentity j hsplit labels O l hTorsionQuotient d i a v).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CompactKernels
