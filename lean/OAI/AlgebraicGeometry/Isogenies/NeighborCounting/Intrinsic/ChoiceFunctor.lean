import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation

/-! # Choice Functor -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor

noncomputable section

/-! The enumeration functor is definitionally the original native
neighbor choice functor, with the same elementary modules and groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices

variable {k : Type} [Field k] [CharZero k] {g s : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (q : ℕ) [Fact q.Prime]
  (c : Fin s → Bool) (p : Fin 3 → Fin (s + 1) → (A.scheme ⟶ A.scheme))
  [∀ i v, IsMonHom (p i v)]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

omit [CharZero k] [∀ i v, IsMonHom (p i v)] in
theorem nativeChoiceFunctor_eq (i : Fin 3) :
    HeckeEvaluation.neighborChoiceFunctor A q (0 : Fin (s + 1)) (Fin.cases false c) p i =
      AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor (s + 1) (Reference.ParameterSubspaces.originalChoiceFunctor (A := A.scheme) q c i (p i)) := rfl

def nativeChoiceRepresentation (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) (i : Fin 3) :
    (AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor (s + 1) (Reference.ParameterSubspaces.originalChoiceFunctor (A := A.scheme) q c i (p i))).RepresentableBy
      (HeckeEvaluation.nativeNeighborParameter A q (0 : Fin (s + 1)) (Fin.cases false c) p hTorsionQuotient i).parameter :=
  (nativeChoiceFunctor_eq A q c p i) ▸
    (HeckeEvaluation.nativeNeighborParameter A q (0 : Fin (s + 1)) (Fin.cases false c) p hTorsionQuotient i).represents

def nativeEvaluatedSubspaceEquiv (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) (i : Fin 3)
    (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField k
      (HeckeEvaluation.nativeNeighborParameter A q (0 : Fin (s + 1)) (Fin.cases false c) p hTorsionQuotient i).parameter)
    (K : Type) [Field K] [IsAlgClosed K] (φ : d.carrier →+* K)
    (coordinates : ∀ v : Fin s,
      Additive (d.extendedParameterBase K φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v.succ)) ≃+
        (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i))) :
    ULift (Fin d.count) ≃
      {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
        (Additive (d.extendedParameterBase K φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0)))) //
        Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} := by
  have hg (v : Fin (s + 1)) := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale (q ^ HeckeExponents.neighborLevel i) (p i v)
    (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of k)))
      (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _) hTorsionQuotient)
  let : ∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v)).hom := fun v => (hg v).1
  let : ∀ v, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v)).hom := fun v => (hg v).2
  exact Reference.ParameterSubspaces.originalParameterSubspaceEquiv (A := A.scheme) q c i (p i)
    (nativeChoiceRepresentation A q c p hTorsionQuotient i) d K φ coordinates

theorem nativeEvaluatedSubspaceEquiv_membership (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) (i : Fin 3)
    (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField k
      (HeckeEvaluation.nativeNeighborParameter A q (0 : Fin (s + 1)) (Fin.cases false c) p hTorsionQuotient i).parameter)
    (K : Type) [Field K] [IsAlgClosed K] (φ : d.carrier →+* K)
    (coordinates : ∀ v : Fin s,
      Additive (d.extendedParameterBase K φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v.succ)) ≃+
        (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))
    (a : ULift (Fin d.count))
    (y : ActiveTorsionChoices.killedSubgroup q (Additive (d.extendedParameterBase K φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0)))) :
    y ∈ (nativeEvaluatedSubspaceEquiv A q c p hTorsionQuotient i d K φ coordinates a).val ↔
      y.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i) (p i 0) ∈
        (Reference.ParameterSubspaces.evaluatedTuple q c i (p i) (nativeChoiceRepresentation A q c p hTorsionQuotient i) d a 0).val.subgroup.points
          (d.extendedParameterBase K φ) (d.parameterExtensionMap K φ) := by
  have hg (v : Fin (s + 1)) := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale (q ^ HeckeExponents.neighborLevel i) (p i v)
    (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of k)))
      (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _) hTorsionQuotient)
  let : ∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v)).hom := fun v => (hg v).1
  let : ∀ v, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v)).hom := fun v => (hg v).2
  exact Reference.ParameterSubspaces.originalParameterSubspaceEquiv_membership q c i (p i)
    (nativeChoiceRepresentation A q c p hTorsionQuotient i) d K φ coordinates a y

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor
