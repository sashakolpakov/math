import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.PointOrbits

/-! # Affine Orbits -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.AffineOrbits.IntegralAuxiliaryAction

noncomputable section

section

/-! Invariance under the actual auxiliary relation is equivalent to
invariance under each constructed constant-label automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem invariant_iff_relabel (W : X.left.Opens) :
    (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left ⁻¹ᵁ W = (ActionSpace.IntegralAuxiliaryAction.target U hU).left ⁻¹ᵁ W ↔
      ∀ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, (U.auxiliaryRelabelMap hU σ).left ⁻¹ᵁ W = W := by
  constructor
  · intro h σ
    ext x
    obtain ⟨r, hr, ht⟩ := (PointOrbits.IntegralAuxiliaryAction.related_iff_relabel U hU x
      ((U.auxiliaryRelabelMap hU σ).left x)).mpr ⟨σ, rfl⟩
    have he := Iff.of_eq (congrArg (fun V => r ∈ V) h)
    change (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left r ∈ W ↔ (ActionSpace.IntegralAuxiliaryAction.target U hU).left r ∈ W at he
    rw [hr, ht] at he
    exact he.symm
  · intro h
    ext r
    obtain ⟨σ, hσ⟩ := (PointOrbits.IntegralAuxiliaryAction.related_iff_relabel U hU
      ((ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left r) ((ActionSpace.IntegralAuxiliaryAction.target U hU).left r)).mp ⟨r, rfl, rfl⟩
    have he := Iff.of_eq (congrArg (fun V => (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left r ∈ V) (h σ))
    change (U.auxiliaryRelabelMap hU σ).left ((ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left r) ∈ W ↔
      (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left r ∈ W at he
    rw [hσ] at he
    exact he.symm

end

/-! An invariant affine cover gives affine neighborhoods of every
orbit of the actual auxiliary relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem affine_orbits_of_relabel_cover {I : Type} (V : I → X.left.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L, ∀ i,
      (U.auxiliaryRelabelMap hU σ).left ⁻¹ᵁ V i = V i) (x : X.left) :
    ∃ W : X.left.Opens, IsAffineOpen W ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left x y → y ∈ W := by
  have hx : x ∈ iSup V := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨V i, hV i, fun y hy => ?_⟩
  obtain ⟨σ, hσ⟩ := (PointOrbits.IntegralAuxiliaryAction.related_iff_relabel U hU x y).mp hy
  have hx' : x ∈ (U.auxiliaryRelabelMap hU σ).left ⁻¹ᵁ V i := by rw [hInv]; exact hi
  exact (congrArg (fun z => z ∈ V i) hσ).mp hx'

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.AffineOrbits.IntegralAuxiliaryAction
