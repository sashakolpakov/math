import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.Enumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration

/-! # Parameter Subspaces -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces

noncomputable section

/-! Attach the exhaustive geometric chosen-block enumeration to the
original finite-evaluation labels. Its membership formula is expressed
in the original evaluated subgroup after the actual field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.ParameterEnumeration.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.Enumeration.Neighbor

variable {k : Type} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  (q : ℕ) [Fact q.Prime] {s : ℕ} (c : Fin s → Bool) (i : Fin 3)
  (p : Fin (s + 1) → (A ⟶ A)) [∀ v, IsMonHom (p v)]
  [∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]
  [∀ v, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

abbrev originalChoiceFunctor (v : Fin (s + 1)) :=
  AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor A (q ^ HeckeExponents.neighborLevel i)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) (p v)

variable {X : Over (Spec (.of k))}
  (repr : (AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor (s + 1) (originalChoiceFunctor q c i p)).RepresentableBy X)
  (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField k X)
  (K : Type) [Field K] [IsAlgClosed K] (φ : d.carrier →+* K)

def evaluatedTuple (a : ULift (Fin d.count)) :=
  AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates (s + 1) (originalChoiceFunctor q c i p)
    (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k d.carrier)))))
    (d.evaluatedChoiceEquiv _ repr a)

def extendedTupleEquiv : ULift (Fin d.count) ≃
    (∀ v, Geometric.Enumeration.Neighbor.originalChoice q c i p K (d.extendedParameterBase K φ).hom v) :=
  (d.extendedChoiceEquiv K φ _ repr).trans
    (AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates (s + 1) (originalChoiceFunctor q c i p)
      (.op (d.extendedParameterBase K φ)))

omit [∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]
  [∀ v, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom] [IsAlgClosed K]
  [IsCommMonObj A] [∀ v, IsMonHom (p v)] in
theorem extendedTupleEquiv_subgroup (a : ULift (Fin d.count)) (v : Fin (s + 1)) :
    (extendedTupleEquiv q c i p repr d K φ a v).val.subgroup =
      ((evaluatedTuple q c i p repr d a v).val.subgroup).baseChange (d.parameterExtensionMap K φ) := by
  change (AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates (s + 1) (originalChoiceFunctor q c i p)
    (.op (d.extendedParameterBase K φ)) (d.extendedChoiceEquiv K φ _ repr a) v).val.subgroup = _
  rw [Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedChoiceEquiv_natural, AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates_natural]
  rfl

variable (coordinates : ∀ v : Fin s,
  Additive (d.extendedParameterBase K φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v.succ)) ≃+
    (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

def originalParameterSubspaceEquiv : ULift (Fin d.count) ≃
    {L : Submodule (ZMod q)
      (ActiveTorsionChoices.killedSubgroup q (Additive (d.extendedParameterBase K φ ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p 0)))) //
      Module.finrank (ZMod q) L = HeckeExponents.neighborLevel i} :=
  (extendedTupleEquiv q c i p repr d K φ).trans
    (Geometric.Enumeration.Neighbor.originalTupleSubspaceEquiv q c i p K (d.extendedParameterBase K φ).hom coordinates)

theorem originalParameterSubspaceEquiv_membership (a : ULift (Fin d.count))
    (x : ActiveTorsionChoices.killedSubgroup q (Additive (d.extendedParameterBase K φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p 0)))) :
    x ∈ (originalParameterSubspaceEquiv q c i p repr d K φ coordinates a).val ↔
      x.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i) (p 0) ∈
        (evaluatedTuple q c i p repr d a 0).val.subgroup.points
          (d.extendedParameterBase K φ) (d.parameterExtensionMap K φ) := by
  refine (Geometric.Enumeration.Neighbor.originalTupleSubspaceEquiv_membership q c i p K (d.extendedParameterBase K φ).hom
    coordinates (extendedTupleEquiv q c i p repr d K φ a) x).trans ?_
  rw [extendedTupleEquiv_subgroup]
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces
