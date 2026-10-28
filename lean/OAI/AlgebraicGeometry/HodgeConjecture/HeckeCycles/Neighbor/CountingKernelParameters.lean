import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

/-! # Counting Kernel Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingKernelParameters.CM

noncomputable section

/-! NeighborCounting's original evaluated labels classify actual chosen kernels of
its generic PEL source. The arithmetic projectors are identified by the
proved base-change equation for the original integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
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

omit [CharZero L] [IsFractionRing R L] in
theorem generic_projector (n : ℕ) (τ : Gal(E/ℚ)) :
    Intrinsic.KernelChoice.CM.projector j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l) n τ =
      (l.genericAction (L := L)).map (j.projector iota hsplit n τ) := by
  change AbelianScheme.TateComparison.End.endSchemeMap _ (((Isogenies.NeighborCounting.ActionFamilyComparison.Family.actionFamily l.actionData).pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R L)))).action _) = _
  rw [AbelianScheme.TateComparison.PEL.PELFamilyData.pullback_action_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
  rfl

local instance heckeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v)))

variable (d : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

local notation "base" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d

def parameterEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    Intrinsic.ParameterKernels.CM.Parameters j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l) base
      (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (fun v => labels (.inl v)) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i) :=
  ((d.family (some i)).evaluatedChoiceEquiv
    (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborChoiceFunctor (l.genericPolarized (L := L)).abelian q active multiplicative
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) i)
    (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.nativeNeighborParameter (l.genericPolarized (L := L)).abelian q active multiplicative
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) h_TorsionQuotient i).represents).trans
    ((AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor
      (l.genericPolarized (L := L)).abelian.scheme (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v))
      (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels i v)) (.op base)).trans
      (Equiv.piCongrRight fun v => Intrinsic.ParameterBaseChange.CM.supportCongr
        (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).abelian.scheme (q ^ Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
        (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i v)) _ _
        (generic_projector j hsplit l (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (labels (.inl v))).symm base))

omit [IsFractionRing R L] in
theorem parameterEquiv_subgroup (i : Fin 3) (a : ULift (Fin (d.count (some i)))) (v : Fin s) :
    (parameterEquiv j hsplit labels active multiplicative h_TorsionQuotient l d i a v).val.subgroup =
      (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedChoice j hsplit labels active multiplicative h_TorsionQuotient l d i a v).val.subgroup := rfl

def kernelEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    AbelianScheme.TateComparison.Subgroups.KernelChoices ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback (base).hom)
      (fun v => j.localCharacter iota (labels (.inl v))) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i) :=
  (parameterEquiv j hsplit labels active multiplicative h_TorsionQuotient l d i).trans
    (Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l)
      (𝟙 (Spec (.of L))) base (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (fun v => labels (.inl v))
      (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i))

omit [IsFractionRing R L] in
theorem kernelEquiv_membership (i : Fin 3) (a : ULift (Fin (d.count (some i))))
    (v : Fin s) (T : Over (base).left)
    (z : T ⟶ ((Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback (base).hom).abelian.scheme) :
    z ∈ ((kernelEquiv j hsplit labels active multiplicative h_TorsionQuotient l d i a).val v).atTest T ↔
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv (base).hom
        (Grp.mk (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l).abelian.scheme) T).symm z ∈
          (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.evaluatedChoice j hsplit labels active multiplicative h_TorsionQuotient l d i a v).val.subgroup.points
            ((Over.map (base).hom).obj T) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint base T) :=
  Intrinsic.ParameterKernels.CM.kernelEquiv_membership j iota hsplit (Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.genericSource (L := L) l)
    (𝟙 (Spec (.of L))) base (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (fun v => labels (.inl v))
    (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i)
    (parameterEquiv j hsplit labels active multiplicative h_TorsionQuotient l d i a) v T z

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingKernelParameters.CM
