import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.PointOrbits
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Relation

/-! # Finite Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiniteAffineCover.IntegralAuxiliaryAction

noncomputable section

/-! An affine-neighborhood property supplies a finite invariant affine
open cover of the actual compact auxiliary parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] [X.left.IsSeparated] [CompactSpace X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem exists_finite_invariant_affine_cover (hrigid : U.PrescribedRigid)
    (hAF : ∀ F : Set X.left, F.Finite → ∃ V : X.left.Opens, IsAffineOpen V ∧ F ⊆ V) :
    ∃ (I : Type) (_ : Finite I) (V : I → X.left.Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      (∀ i, (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left ⁻¹ᵁ V i = (ActionSpace.IntegralAuxiliaryAction.target U hU).left ⁻¹ᵁ V i) ∧
      iSup V = ⊤ := by
  classical
  let a := (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
  let t := (ActionSpace.IntegralAuxiliaryAction.target U hU).left
  have hV (x : X.left) : ∃ V : X.left.Opens, IsAffineOpen V ∧
      x ∈ V ∧ a ⁻¹ᵁ V = t ⁻¹ᵁ V := by
    obtain ⟨V, hV, horbit⟩ := hAF _ (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.finite_orbit a t x)
    refine ⟨Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core a t V, PointOrbits.IntegralAuxiliaryAction.affine_core U hU V hV,
      (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.mem_core a t V x).mpr horbit, ?_⟩
    exact Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core_invariant a t (Relation.IntegralAuxiliaryAction.equivalenceRelation U hU hrigid) V
  choose V hV hx hInv using hV
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X.left))
    (fun x => (V x).isOpen) (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun x => V x, fun x => hV x, fun x => hInv x, ?_⟩
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨hys, hxy⟩ := Set.mem_iUnion.mp hy
  exact Opens.mem_iSup.mpr ⟨⟨y, hys⟩, hxy⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiniteAffineCover.IntegralAuxiliaryAction
