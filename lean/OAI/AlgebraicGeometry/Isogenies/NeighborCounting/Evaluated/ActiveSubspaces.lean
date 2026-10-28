import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension

/-! # Active Subspaces -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces

noncomputable section

/-! The active geometric subspace is expressed in the actual q-block
over the original evaluation field. Its comparison uses the original
source torsion splitting and literal field-extension map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPointExtension

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (d : ParameterPoints.Lifts.FiniteEvaluationField L (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme q))
  (k : Type) [Field k] (φ : d.carrier →+* k) (τ : Gal(E/ℚ))

abbrev originalEvaluationBase : Over (Spec (.of L)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))

def evaluatedBlockPointsEquiv :
    Additive (originalEvaluationBase A d ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) ≃+
      Additive (d.extendedParameterBase k φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) :=
  (SplitBlockPointExtension.fixedPointExtensionGroupEquiv d k φ (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap q (ρ.map (j.projector iota hsplit 1 τ)))).toAdditive

theorem evaluatedBlockPointsEquiv_apply
    (a : Additive (originalEvaluationBase A d ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) :
    (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ a).toMul =
      d.parameterExtensionMap k φ ≫ a.toMul := rfl

def evaluatedActiveSubspaceEquiv (m : ℕ) (hm : 1 ≤ m) (r : ℕ) :
    {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive (d.extendedParameterBase k φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (ρ.map (j.projector iota hsplit m τ))))) //
      Module.finrank (ZMod q) V = r} ≃
    {V : Submodule (ZMod q)
      (Additive (originalEvaluationBase A d ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) //
      Module.finrank (ZMod q) V = r} :=
  (Intrinsic.ActiveSubspaces.nativeActiveSubspaceEquiv j iota hsplit A ρ (d.extendedParameterBase k φ) m hm τ r).trans
    (SubspaceCoordinates.dimensionSubspaceEquiv
      (ActiveTypedSubspaces.zmodLinearEquiv q (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ).symm) r)

theorem evaluatedActiveSubspaceEquiv_membership (m : ℕ) (hm : 1 ≤ m) (r : ℕ)
    (V : {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q
      (Additive (d.extendedParameterBase k φ ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (ρ.map (j.projector iota hsplit m τ))))) //
      Module.finrank (ZMod q) V = r})
    (a : Additive (originalEvaluationBase A d ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) :
    a ∈ (evaluatedActiveSubspaceEquiv j iota hsplit A ρ d k φ τ m hm r V).val ↔
      (Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv j iota hsplit A ρ (d.extendedParameterBase k φ) m hm τ).symm
        (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ a) ∈ V.val := by
  refine (SubspaceCoordinates.dimensionSubspaceEquiv_membership
    (ActiveTypedSubspaces.zmodLinearEquiv q (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ).symm) r
    (Intrinsic.ActiveSubspaces.nativeActiveSubspaceEquiv j iota hsplit A ρ (d.extendedParameterBase k φ) m hm τ r V) a).trans ?_
  exact SubspaceCoordinates.dimensionSubspaceEquiv_membership
    (ActiveTypedSubspaces.zmodLinearEquiv q (Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv j iota hsplit A ρ
      (d.extendedParameterBase k φ) m hm τ)) r V
    (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ a)

theorem evaluatedActivePreimage_inclusion (m : ℕ) (hm : 1 ≤ m)
    (a : Additive (originalEvaluationBase A d ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) :
    ((Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv j iota hsplit A ρ (d.extendedParameterBase k φ) m hm τ).symm
      (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ a)).val.toMul ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (ρ.map (j.projector iota hsplit m τ)) =
    d.parameterExtensionMap k φ ≫
      (a.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ))) := by
  have h := Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv_inclusion j iota hsplit A ρ (d.extendedParameterBase k φ) m hm τ
    ((Intrinsic.ActiveSubspaces.nativeBlockKilledPrimeEquiv j iota hsplit A ρ (d.extendedParameterBase k φ) m hm τ).symm
      (evaluatedBlockPointsEquiv j iota hsplit A ρ d k φ τ a))
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm.trans (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveSubspaces
