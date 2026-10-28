import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Cover Unit Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoverUnitBaseChange

noncomputable section

/-! A cover and its invariance equations valid away from a coefficient
become an actual invariant affine cover after that coefficient maps to a unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem invariant_affine_cover_baseChange_of_unit
    {R R' : Type} [CommRing R] [CommRing R'] {I G : Type}
    (Y : Over (Spec (.of R))) (V : I → Y.left.Opens) (a : G → (Y ⟶ Y)) (r : R)
    (hV : ∀ i, IsAffineOpen (V i))
    (hcover : ∀ x : Y.left, r ∉ (Y.hom x).asIdeal → ∃ i, x ∈ V i)
    (hInv : ∀ g i (x : Y.left), r ∉ (Y.hom x).asIdeal → ((a g).left x ∈ V i ↔ x ∈ V i))
    (φ : R →+* R') (hunit : IsUnit (φ r)) :
    let b := Spec.map (CommRingCat.ofHom φ)
    let q := pullback.fst Y.hom b
    (∀ i, IsAffineOpen (q ⁻¹ᵁ V i)) ∧ (⨆ i, q ⁻¹ᵁ V i) = ⊤ ∧
      (∀ g i, ((Over.pullback b).map (a g)).left ⁻¹ᵁ (q ⁻¹ᵁ V i) = q ⁻¹ᵁ V i) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let Z : Over (Spec (.of R')) := (Over.pullback b).obj Y
  let q := pullback.fst Y.hom b
  have : IsAffineHom b := inferInstance
  have : IsAffineHom q := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback Y.hom b).flip (inferInstanceAs (IsAffineHom b))
  have hr (x : Z.left) : r ∉ (Y.hom (q x)).asIdeal := by
    intro h
    have he : Y.hom (q x) = b (pullback.snd Y.hom b x) :=
      congrArg (fun f : Z.left ⟶ Spec (.of R) => f x) pullback.condition
    have h' : φ r ∈ (pullback.snd Y.hom b x).asIdeal :=
      (congrArg (fun p : Spec (.of R) => r ∈ p.asIdeal) he).mp h
    exact (pullback.snd Y.hom b x).isPrime.ne_top
      ((pullback.snd Y.hom b x).asIdeal.eq_top_of_isUnit_mem h' hunit)
  refine ⟨fun i => (hV i).preimage q, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := hcover (q x) (hr x)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro g i
    ext x
    have he : q (((Over.pullback b).map (a g)).left x) = (a g).left (q x) :=
      congrArg (fun f : Z.left ⟶ Y.left => f x) (pullback.lift_fst _ _ _)
    change q (((Over.pullback b).map (a g)).left x) ∈ V i ↔ q x ∈ V i
    rw [he]
    exact hInv g i (q x) (hr x)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoverUnitBaseChange
