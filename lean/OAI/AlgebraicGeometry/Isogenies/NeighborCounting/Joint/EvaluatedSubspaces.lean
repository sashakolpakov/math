import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip

/-! # Evaluated Subspaces -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluatedSubspaces

noncomputable section

/-! Compose the native choice enumeration with original source-torsion
evaluation before specializing to a full PEL lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor

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

def jointProjectorSubspaceEquiv :
    {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive ((d.family (some i)).extendedParameterBase k φ ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0)))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} ≃
    {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive ((d.family none).extendedParameterBase k φ ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ))))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} :=
  SubspaceCoordinates.killedPointSubspaceEquiv q
    (ActionRoundTrip.nativeBlockPointEquivOfEq
      (T := (d.family none).extendedParameterBase k φ) (q ^ HeckeExponents.neighborLevel i) hp) (HeckeExponents.neighborLevel i)

def jointActivePointEquiv :
    ActiveTorsionChoices.killedSubgroup q (Additive ((d.family (some i)).extendedParameterBase k φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0))) ≃+
    Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) :=
  (Intrinsic.ActiveLevel.killedSubgroupEquiv q
    (ActionRoundTrip.nativeBlockPointEquivOfEq
      (T := (d.family none).extendedParameterBase k φ) (q ^ HeckeExponents.neighborLevel i) hp)).trans
    ((Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv j iota hsplit A ρ
      ((d.family none).extendedParameterBase k φ) (HeckeExponents.neighborLevel i)
      (Nat.succ_le_succ (Nat.zero_le i.val)) τ).trans
      (Evaluated.ActiveSubspaces.evaluatedBlockPointsEquiv j iota hsplit A ρ (d.family none) k φ τ).symm)

def jointActiveEvaluationSubspaceEquiv :
    {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive ((d.family (some i)).extendedParameterBase k φ ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i 0)))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} ≃
    {V : Submodule (ZMod q)
      (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} :=
  SubspaceCoordinates.dimensionSubspaceEquiv
    (ActiveTypedSubspaces.zmodLinearEquiv q
      (jointActivePointEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp)) (HeckeExponents.neighborLevel i)

def jointEvaluatedSubspaceEquiv : ULift.{0} (Fin (d.count (some i))) ≃
    {V : Submodule (ZMod q)
      (Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) //
      Module.finrank (ZMod q) V = HeckeExponents.neighborLevel i} :=
  (Intrinsic.ChoiceFunctor.nativeEvaluatedSubspaceEquiv A q c p hTorsionQuotient i (d.family (some i)) k φ coordinates).trans
    (jointActiveEvaluationSubspaceEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluatedSubspaces
