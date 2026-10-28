import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluatedSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorSubspaceMembership
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositePointInclusion

/-! # Subspace Membership -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.SubspaceMembership

noncomputable section

/-! The original finite parameter enumeration has the expected
membership predicate on original evaluation-field q-block points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluatedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorSubspaceMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] [CharZero L] {g s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (c : Fin s → Bool) (p : Fin 3 → Fin (s + 1) → (A.scheme ⟶ A.scheme))
  [∀ i v, IsMonHom (p i v)] (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (d : IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q 0 (Fin.cases false c) p hTorsionQuotient))
  (i : Fin 3) (k : Type) [Field k] [IsAlgClosed k] (φ : d.carrier →+* k)
  (τ : Gal(E/ℚ)) (hp : p i 0 = ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ))
  (coordinates : ∀ v : Fin s,
    Additive ((d.family (some i)).extendedParameterBase k φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v.succ)) ≃+ (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

variable (a : ULift (Fin (d.count (some i))))
  (z : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))))

def jointActivePreimage :=
  (EvaluatedSubspaces.jointActivePointEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp).symm z

omit [IsAlgClosed k] in
theorem jointActivePreimage_inclusion :
    ((jointActivePreimage j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp z).val.toMul :
      (d.family (some i)).extendedParameterBase k φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0)) ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i) (p i 0) =
    (d.family none).parameterExtensionMap k φ ≫
      (z.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ))) := by
  have h := CompositePointInclusion.inverse_composite_inclusion
    (Intrinsic.ActiveLevel.killedSubgroupEquiv q (ActionRoundTrip.nativeBlockPointEquivOfEq
      (T := (d.family none).extendedParameterBase k φ) (q ^ HeckeExponents.neighborLevel i) hp))
    (Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv j iota hsplit A ρ ((d.family none).extendedParameterBase k φ)
      (HeckeExponents.neighborLevel i) (Nat.succ_le_succ (Nat.zero_le i.val)) τ)
    (Evaluated.ActiveSubspaces.evaluatedBlockPointsEquiv j iota hsplit A ρ (d.family none) k φ τ)
    (fun y => y.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i) (p i 0))
    (fun y => y.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i)
      (ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ)))
    (fun w => (d.family none).parameterExtensionMap k φ ≫
      (w.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ))))
    (fun y => ProjectorSubspaceMembership.nativeBlockPointEquivOfEq_symm_inclusion (q ^ HeckeExponents.neighborLevel i) hp y.val)
    (Evaluated.ActiveSubspaces.evaluatedActivePreimage_inclusion j iota hsplit A ρ (d.family none) k φ τ
      (HeckeExponents.neighborLevel i) (Nat.succ_le_succ (Nat.zero_le i.val))) z
  exact h

omit [IsAlgClosed k] in
theorem jointActiveEvaluationSubspaceEquiv_membership
    (V : {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive ((d.family (some i)).extendedParameterBase k φ ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0)))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i}) :
    z ∈ (EvaluatedSubspaces.jointActiveEvaluationSubspaceEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp V).val ↔
      jointActivePreimage j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp z ∈ V.val := by
  exact SubspaceCoordinates.dimensionSubspaceEquiv_membership
    (ActiveTypedSubspaces.zmodLinearEquiv q
      (EvaluatedSubspaces.jointActivePointEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp)) (HeckeExponents.neighborLevel i) V z

theorem jointEvaluatedSubspaceEquiv_membership :
    z ∈ (EvaluatedSubspaces.jointEvaluatedSubspaceEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates a).val ↔
      (d.family none).parameterExtensionMap k φ ≫
        (z.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ))) ∈
      (Reference.ParameterSubspaces.evaluatedTuple q c i (p i) (Intrinsic.ChoiceFunctor.nativeChoiceRepresentation A q c p hTorsionQuotient i)
        (d.family (some i)) a 0).val.subgroup.points
        ((d.family (some i)).extendedParameterBase k φ) ((d.family (some i)).parameterExtensionMap k φ) := by
  have h₁ := jointActiveEvaluationSubspaceEquiv_membership j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp z
    (Intrinsic.ChoiceFunctor.nativeEvaluatedSubspaceEquiv A q c p hTorsionQuotient i (d.family (some i)) k φ coordinates a)
  have h₃ := Intrinsic.ChoiceFunctor.nativeEvaluatedSubspaceEquiv_membership A q c p hTorsionQuotient i (d.family (some i))
    k φ coordinates a (jointActivePreimage j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp z)
  erw [jointActivePreimage_inclusion j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp z] at h₃
  exact h₁.trans h₃

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.SubspaceMembership
