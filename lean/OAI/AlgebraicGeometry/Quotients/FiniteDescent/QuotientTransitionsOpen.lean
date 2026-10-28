import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantOpensEq

/-! # Quotient Transitions Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientTransitionsOpen.Construction.QuotientTransitions

/-!
# Canonical open transitions between local quotients

An open immersion of object charts that restricts the source of the relation
induces a unique open immersion of quotient charts. Its square is cartesian.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R X Q R' X' Q' : Scheme.{u}} {s t : R ⟶ X}
    (q : X ⟶ Q) (hk : IsKernelPair q s t)
    (i : X' ⟶ X) [IsOpenImmersion i] (j : R' ⟶ R) (s' t' : R' ⟶ X')
    (hs : IsPullback s' j i s) (ht : t' ≫ i = j ≫ t)

include hk hs ht

/-- If the target of a source-restricted relation remains in an open chart,
that chart is invariant under the entire equivalence relation. -/
theorem opensRange_invariant : s ⁻¹ᵁ i.opensRange = t ⁻¹ᵁ i.opensRange := by
  have forward (r : R) (hr : s r ∈ Set.range i) : t r ∈ Set.range i := by
    obtain ⟨x, hx⟩ := hr
    obtain ⟨r', _, hj⟩ := Scheme.exists_preimage_of_isPullback hs x r hx
    refine ⟨t' r', ?_⟩
    rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply, hj]
  let invR := hk.lift t s hk.w.symm
  have hinvs (r : R) : s (invR r) = t r :=
    congrArg (fun f => f r) (hk.lift_fst t s hk.w.symm)
  have hinvt (r : R) : t (invR r) = s r :=
    congrArg (fun f => f r) (hk.lift_snd t s hk.w.symm)
  ext r
  change s r ∈ Set.range i ↔ t r ∈ Set.range i
  refine ⟨forward r, fun hr => ?_⟩
  simpa only [hinvt] using forward (invR r) (by simpa only [hinvs] using hr)

variable [Flat q] [QuasiCompact q] [Surjective q]

/-- An effective quotient of an invariant open relation embeds openly in the
larger quotient. Both the transition and its cartesian property are derived
from the local kernel pairs. -/
theorem existsUnique_open_transition (q' : X' ⟶ Q') [EffectiveEpi q']
    (hk' : IsKernelPair q' s' t') :
    ∃! f : Q' ⟶ Q,
      q' ≫ f = i ≫ q ∧ IsOpenImmersion f ∧ IsPullback q' i f q := by
  let W := i.opensRange
  have hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W := opensRange_invariant q hk i j s' t' hs ht
  let D := InvariantOpensEq.Construction.InvariantOpens.descend q hk W hW
  let q₀ : X' ⟶ D.toScheme := i.isoOpensRange.hom ≫
    InvariantOpensEq.Construction.InvariantOpens.restrictProjection q hk W hW
  have hc : IsPullback q₀ i D.ι q := by
    refine (InvariantOpensEq.Construction.InvariantOpens.restrictProjection_isPullback q hk W hW).of_iso
      i.isoOpensRange.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ (by simp [D]) (by simp)
    · simp [q₀]
    · simp [W]
  have hk₀ : IsKernelPair q₀ s' t' := by
    have hlarge : IsPullback s' (t' ≫ i) (q₀ ≫ D.ι) q := by
      rw [ht, hc.w]
      exact hs.paste_vert hk
    apply IsPullback.of_bot hlarge _ hc
    apply (cancel_mono D.ι).mp
    simp only [Category.assoc, hc.w]
    rw [← Category.assoc, hs.w, Category.assoc, hk.w, ← Category.assoc, ← ht, Category.assoc]
  have : EffectiveEpi q₀ := by dsimp [q₀]; infer_instance
  obtain ⟨e, he, _⟩ := Quotient.Construction.QuotientDescent.existsUnique_iso q' q₀ hk' hk₀
  let f := e.hom ≫ D.ι
  have hf : q' ≫ f = i ≫ q := by
    rw [show f = e.hom ≫ D.ι from rfl, ← Category.assoc, he, hc.w]
  have hpb : IsPullback q' i f q := by
    refine hc.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      ?_ (by simp) ?_ (by simp)
    · simp [← he]
    · simp [f]
  refine ⟨f, ⟨hf, inferInstance, hpb⟩, ?_⟩
  intro f' hf'
  exact (cancel_epi q').mp (hf'.1.trans hf.symm)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.QuotientTransitionsOpen.Construction.QuotientTransitions
