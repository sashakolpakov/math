import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CompactKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.KernelDetection

/-! # Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison

noncomputable section

/-! Identify the original complete evaluated kernel using its unchanged active choice, with all compact and opposite factors derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection.Neighbor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.KernelDetection.Neighbor

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

variable (i : Fin 3) (a : ULift (Fin (d.count (some i))))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (w : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i w)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false (O.compact x)) i w)

local instance oppositeProjector_group (w : Fin (s + 1)) :
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) (s + 1) (Intrinsic.KernelLabels.nativeKernelLabels labels) w) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (w, true)))

def originalCompleteKernelIdentity :=
  let hg := fun w : Fin (s + 1) => Intrinsic.ParameterEnumeration.originalNeighborBlockGeometry j hsplit labels l hTorsionQuotient i w
  letI : ∀ w, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i w)).hom := fun w => (hg w).1
  letI : ∀ w, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i w)).hom := fun w => (hg w).2
  let c : Fin (s + 1) → Bool := Fin.cases false (O.compact x)
  let F := Intrinsic.ReductionSpecification.evaluatedChoice (L := L) j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) (0 : Fin (s + 1))
    c hTorsionQuotient l d i a
  PLift.up (KernelDetection.Neighbor.neighborFullKernel_eq q (O.compact x) i
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) (s + 1) (Intrinsic.KernelLabels.nativeKernelLabels labels))
    (Intrinsic.ReductionSpecification.genericCanonicalPairing (L := L) j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) l i)
    F
    (fun v k _ _ b₀ _ => Lifted.BlockCoordinates.liftedNativeBlockCoordinates j hsplit labels O l hTorsionQuotient
      (HeckeExponents.neighborLevel i) v.succ k b₀))

omit [IsFractionRing R L] in
theorem originalCompleteKernel_eq :
    type_of% (originalCompleteKernelIdentity j hsplit labels O l hTorsionQuotient d i a).down :=
  (originalCompleteKernelIdentity j hsplit labels O l hTorsionQuotient d i a).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison
