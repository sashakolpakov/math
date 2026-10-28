import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric Fiber Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.GeometricFiberFiniteness

noncomputable section

/-! Finiteness of a proper morphism is detected on all algebraically closed field-valued fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem finite_preimage_of_finite_fieldPullback (f : X ⟶ Y) {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ Y) [IsFinite (Limits.pullback.snd f a)]
    (k : Spec (.of K)) : (f ⁻¹' {a k}).Finite := by
  have : Finite (Limits.pullback f a : Scheme.{u}) := by
    apply Finite.of_finite_univ
    simpa only [Set.preimage_univ] using
      (Limits.pullback.snd f a).finite_preimage (Set.finite_univ : (Set.univ : Set (Spec (.of K))).Finite)
  apply (Set.finite_range (Limits.pullback.fst f a)).subset
  intro z hz
  change f z = a k at hz
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback z k hz
  exact ⟨w, hw⟩

theorem proper_isFinite_of_geometric_fieldPullbacks (f : X ⟶ Y) [IsProper f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Y),
      IsFinite (Limits.pullback.snd f a)) : IsFinite f := by
  have hf (y : Y) : (f ⁻¹' {y}).Finite := by
    let K := AlgebraicClosure (Y.residueField y)
    let a : Spec (.of K) ⟶ Y :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y
    let k : Spec (.of K) := Classical.choice inferInstance
    have : IsFinite (Limits.pullback.snd f a) := h K a
    have hk : a k = y := Y.fromSpecResidueField_apply y _
    exact hk ▸ finite_preimage_of_finite_fieldPullback f a k
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.GeometricFiberFiniteness
