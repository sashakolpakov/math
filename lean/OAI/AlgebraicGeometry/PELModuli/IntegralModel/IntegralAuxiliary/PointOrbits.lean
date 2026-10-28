import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionPoints
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Invariant
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Point Orbits -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.PointOrbits.IntegralAuxiliaryAction

noncomputable section

section

/-! The underlying orbits of the integral relation are exactly the
orbits of its constructed constant-label automorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem related_iff_relabel (x y : X.left) :
    Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left x y ↔
      ∃ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, (U.auxiliaryRelabelMap hU σ).left x = y := by
  constructor
  · rintro ⟨r, rfl, rfl⟩
    let Z := ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L
    let k := Z.left.residueField r
    let a := Z.left.fromSpecResidueField r
    let W : Over (Spec (.of R)) := Over.mk (a ≫ Z.hom)
    let p : W ⟶ Z := Over.homMk a rfl
    have : IsReduced W.left := inferInstanceAs (IsReduced (Spec (.of k)))
    have : Subsingleton W.left := inferInstanceAs (Subsingleton (Spec (.of k)))
    let z : W.left := IsLocalRing.closedPoint k
    let b := ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L W p
    let σ := b z
    have hb : b = LocallyConstant.const W.left σ := by
      apply LocallyConstant.ext
      intro w
      exact congrArg b (Subsingleton.elim w z)
    have he := ActionSpace.IntegralAuxiliaryAction.target_points U hU W p
    change p ≫ ActionSpace.IntegralAuxiliaryAction.target U hU = U.auxiliaryRelabelAt hU (p ≫ ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) b at he
    rw [hb, U.auxiliaryRelabelAt_const hU] at he
    have hv := congrArg (fun f : W ⟶ X => f.left z) he
    change (ActionSpace.IntegralAuxiliaryAction.target U hU).left (p.left z) =
      (U.auxiliaryRelabelMap hU σ).left ((ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (p.left z)) at hv
    have hp : p.left z = r := Z.left.fromSpecResidueField_apply r _
    rw [hp] at hv
    exact ⟨σ, hv.symm⟩
  · rintro ⟨σ, hσ⟩
    let p := ActionPoints.IntegralAuxiliaryAction.pair (𝟙 X) (LocallyConstant.const X.left σ)
    have hs : p ≫ ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L = 𝟙 X := ActionPoints.IntegralAuxiliaryAction.pair_source _ _
    have ht : p ≫ ActionSpace.IntegralAuxiliaryAction.target U hU = U.auxiliaryRelabelMap hU σ := by
      rw [ActionPoints.IntegralAuxiliaryAction.pair_target, U.auxiliaryRelabelAt_const hU, Category.id_comp]
    exact ⟨p.left x, congrArg (fun f : X ⟶ X => f.left x) hs,
      (congrArg (fun f : X ⟶ X => f.left x) ht).trans hσ⟩

end

/-! On a separated parameter, the invariant core of an affine open
is affine: it is a finite intersection of its translates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem core_eq_iInf (V : X.left.Opens) :
    Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left V =
      ⨅ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, (U.auxiliaryRelabelMap hU σ).left ⁻¹ᵁ V := by
  ext x
  change x ∈ Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left V ↔
    x ∈ ⨅ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, (U.auxiliaryRelabelMap hU σ).left ⁻¹ᵁ V
  rw [Quotients.FiniteDescent.Invariant.Construction.InvariantCore.mem_core]
  simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  constructor
  · intro h σ
    exact h _ ((related_iff_relabel U hU x _).mpr ⟨σ, rfl⟩)
  · intro h y hy
    obtain ⟨σ, rfl⟩ := (related_iff_relabel U hU x y).mp hy
    exact h σ

theorem affine_core [X.left.IsSeparated] (V : X.left.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.core (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left V) := by
  rw [core_eq_iInf U hU]
  apply IsAffineOpen.iInf
  intro σ
  have : IsIso (U.auxiliaryRelabelMap hU σ).left :=
    ((Over.forget (Spec (.of R))).mapIso (U.auxiliaryRelabelIso hU σ)).isIso_hom
  exact hV.preimage_of_isIso (U.auxiliaryRelabelMap hU σ).left

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.PointOrbits.IntegralAuxiliaryAction
