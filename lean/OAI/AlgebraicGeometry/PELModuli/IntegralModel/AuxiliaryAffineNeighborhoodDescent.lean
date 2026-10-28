import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.PointOrbits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InvariantAffine
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Auxiliary Affine Neighborhood Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AuxiliaryAffineNeighborhoodDescent.IntegralAuxiliaryAction

noncomputable section

/-! Affine neighborhoods of finite subsets descend through the actual
auxiliary quotient over a field. Take the affine invariant core of one
neighborhood containing the complete finite inverse image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* K} {X : Over (Spec (.of K))}
    [IsReduced X.left] [X.left.IsSeparated]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO L N X) (hU : U.IsFine)

theorem finite_set_affine_neighborhood_descends {Y : Scheme.{0}} (q : X.left ⟶ Y)
    [IsFinite q] [Flat q] [Surjective q]
    (hk : IsKernelPair q (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    (hX : ∀ F : Set X.left, F.Finite → ∃ V : X.left.Opens, IsAffineOpen V ∧ F ⊆ V)
    (F : Set Y) (hF : F.Finite) : ∃ V : Y.Opens, IsAffineOpen V ∧ F ⊆ V := by
  let a := (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
  let t := (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left
  let H := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of K)) (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  let := H.hom.appTop.hom.toAlgebra
  have : Module.Finite Γ(Spec (.of K), ⊤) Γ(H.left, ⊤) := H.hom.finite_appTop
  let basis := Module.finBasis Γ(Spec (.of K), ⊤) Γ(H.left, ⊤)
  obtain ⟨V, hV, hFV⟩ := hX (q ⁻¹' F) (q.finite_preimage hF)
  let W := Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core a t V
  have hW : IsAffineOpen W := IntegralAuxiliary.PointOrbits.IntegralAuxiliaryAction.affine_core U hU V hV
  let e := hk.equivalenceRelation q a t (pullback.isLimit t a)
  have hInv : a ⁻¹ᵁ W = t ⁻¹ᵁ W := Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core_invariant a t e V
  refine ⟨Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens.descend q hk W hInv, ?_, ?_⟩
  · exact AbelianScheme.IsogenyQuotient.InvariantAffine.Construction.invariantAffineOpen_descends q a t hk H.hom X.hom
      (prod.snd : IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L ⟶ H).left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source_isPullback X (3 * s) L) basis W hW hInv
  · intro y hy
    obtain ⟨x, hx⟩ := (inferInstance : Surjective q).surj y
    refine ⟨x, ?_, hx⟩
    apply (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.mem_core a t V x).mpr
    intro z hz
    obtain ⟨r, hr, ht⟩ := hz
    have hq : q x = q z := by
      have he : q (a r) = q (t r) := congrArg (fun f => f r) hk.w
      exact (congrArg q hr).symm.trans (he.trans (congrArg q ht))
    apply hFV
    change q z ∈ F
    rw [← hq, hx]
    exact hy

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AuxiliaryAffineNeighborhoodDescent.IntegralAuxiliaryAction
