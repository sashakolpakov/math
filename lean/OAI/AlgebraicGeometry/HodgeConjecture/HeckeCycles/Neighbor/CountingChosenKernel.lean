import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingKernelParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.BlockIntersection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

/-! # Counting Chosen Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingChosenKernel.CM

noncomputable section

/-! The actual NeighborCounting PEL quotient has precisely its original chosen
kernel on every split block. This is derived from its complete relative
kernel and the orthogonality of the actual CMPoints projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

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

local instance oppositeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) s labels v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inr v)))

variable (d : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

local notation "base" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d

variable [Algebra R d.carrier] [IsScalarTower R L d.carrier]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR R d.carrier) (i : Fin 3) (a : ULift (Fin (d.count (some i))))
  (Q : Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d V i a)

omit [IsFractionRing R L] [IsScalarTower R L d.carrier] in
include Q in
theorem quotient_chosen_kernel (v : Fin s) :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel Q.quotient.isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback (base).hom)
        (j.localCharacter iota (labels (.inl v))) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)) =
      (CountingKernelParameters.CM.kernelEquiv j hsplit labels active multiplicative h_TorsionQuotient l d i a).val v := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro T
  ext z
  let e := (l.genericPolarized (L := L)).abelian.baseChangePointsMulEquiv (base).hom T
  have hq : z ≫ Q.quotient.isogeny.hom = 1 ↔ e z ∈
      (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a).points
        ((Over.map (base).hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint base T) :=
    AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints.Construction.nativeQuotient_kernel_membership (l.genericPolarized (L := L)).abelian base _ Q.model
      Q.quotient.isogeny Q.kernel T z
  have hc (hz : z ∈ (AbelianScheme.TateComparison.Subgroups.splitBlock ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback (base).hom)
      (j.localCharacter iota (labels (.inl v))) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)).atTest T) :
      e z ∈ (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a).points
        ((Over.map (base).hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint base T) ↔
      e z ∈ (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedChoice j hsplit labels active multiplicative h_TorsionQuotient l d i a v).val.subgroup.points
        ((Over.map (base).hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint base T) := by
    have hb : e z ∈ (AbelianScheme.TateComparison.Subgroups.splitBlock (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l)
        (j.localCharacter iota (labels (.inl v))) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)).atTest
          ((Over.map (base).hom).obj T) := by
      have hz' := hz
      rw [← AbelianScheme.TateComparison.SplitSubgroups.splitBlock_pullback] at hz'
      exact hz'
    have hf := ((PELModuli.CMPoints.BlocksProjectors.mem_block_iff_fixed j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).abelian
      (AbelianScheme.TateComparison.PELAdapters.actionFromEnd (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).action) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v))
      ((Over.map (base).hom).obj T) (e z)).mp hb).2
    change e z ≫ Intrinsic.KernelChoice.CM.projector j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l)
      (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v)) = e z at hf
    rw [CountingKernelParameters.CM.generic_projector] at hf
    exact AbelianScheme.IsogenyQuotient.Kernel.BlockIntersection.Construction.choiceFullKernel_chosen_membership (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) s
      (fun w => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i w))
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) s labels)
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) s labels)
      (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericCanonicalPairing j hsplit labels l i)
      (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedChoice j hsplit labels active multiplicative h_TorsionQuotient l d i a)
      (fun w t hwt => AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy.Construction.l45_choice_torsion_orthogonal j iota hsplit
        (l.genericPolarized (L := L)).abelian (l.genericAction (L := L))
        (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) s labels t w hwt.symm)
      ((Over.map (base).hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint base T) v (e z) hf
  have hp := CountingKernelParameters.CM.kernelEquiv_membership j hsplit labels active multiplicative
    h_TorsionQuotient l d i a v T z
  change (z ≫ Q.quotient.isogeny.hom = 1 ∧ z ∈
    (AbelianScheme.TateComparison.Subgroups.splitBlock ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback (base).hom)
      (j.localCharacter iota (labels (.inl v))) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)).atTest T) ↔ _
  constructor
  · intro hz
    exact hp.mpr ((hc hz.2).mp (hq.mp hz.1))
  · intro hz
    have hb := (CountingKernelParameters.CM.kernelEquiv j hsplit labels active multiplicative
      h_TorsionQuotient l d i a).property v |>.2.1 T hz
    exact ⟨hq.mpr ((hc hb).mpr (hp.mp hz)), hb⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingChosenKernel.CM
