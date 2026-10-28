import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.SubspaceMembership

/-! # Coordinate Membership -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateMembership

noncomputable section

/-! Standard-coordinate membership is the membership predicate of the
original evaluated neighbor choice after its specified field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluatedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.SubspaceMembership
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

variable
  (linearCoordinates : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) ≃ₗ[ZMod q] ((Fin 2 → ZMod q) × ZMod q))
  (a : ULift (Fin (d.count (some i))))
  (z : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))))

theorem jointCoordinateSubspaceEquiv_membership :
    linearCoordinates z ∈
      (CoordinateSubspaces.jointCoordinateSubspaceEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates linearCoordinates a).val ↔
      (d.family none).parameterExtensionMap k φ ≫
        (z.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ))) ∈
      (Reference.ParameterSubspaces.evaluatedTuple q c i (p i) (Intrinsic.ChoiceFunctor.nativeChoiceRepresentation A q c p hTorsionQuotient i)
        (d.family (some i)) a 0).val.subgroup.points
        ((d.family (some i)).extendedParameterBase k φ) ((d.family (some i)).parameterExtensionMap k φ) := by
  have h₁ := CoordinateEnumeration.coordinateSubspaceEnumeration_membership (HeckeExponents.neighborLevel i)
    (EvaluatedSubspaces.jointEvaluatedSubspaceEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates)
    linearCoordinates a z
  have h₂ := SubspaceMembership.jointEvaluatedSubspaceEquiv_membership j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates a z
  exact h₁.trans h₂

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateMembership
