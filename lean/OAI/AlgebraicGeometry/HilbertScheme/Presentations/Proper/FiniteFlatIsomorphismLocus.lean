import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FlatIsomorphismLocus
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finite Flat Isomorphism Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteFlatIsomorphismLocus

noncomputable section

/-! Over a proper parameterized target, the condition that a finite flat
morphism becomes an isomorphism on the whole family is represented by an open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B)
variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [IsProper q]

def properFiniteFlatIsomorphismOpen : B.Opens :=
  ⟨(q '' (Finite.FlatIsomorphismLocus.finiteFlatIsomorphismOpen f : Set Y)ᶜ)ᶜ,
    (q.isClosedMap _ (Finite.FlatIsomorphismLocus.finiteFlatIsomorphismOpen f).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_properFiniteFlatIsomorphismOpen (b : B) :
    b ∈ properFiniteFlatIsomorphismOpen f q ↔ ∀ y : Y, q y = b → f.finrank y = 1 := by
  constructor
  · intro h y hy
    by_contra hn
    exact h ⟨y, hn, hy⟩
  · intro h
    rintro ⟨y, hy, he⟩
    exact hy (h y he)

theorem properFiniteFlat_isIso_pullback_iff_range {T : Scheme.{u}} (g : T ⟶ B) :
    IsIso (pullback.snd f (pullback.fst q g)) ↔
      Set.range g ⊆ (properFiniteFlatIsomorphismOpen f q : Set B) := by
  rw [Finite.FlatIsomorphismLocus.finiteFlat_isIso_pullback_iff_range, Scheme.Pullback.range_fst]
  constructor
  · intro h b hb
    obtain ⟨t, rfl⟩ := hb
    apply (mem_properFiniteFlatIsomorphismOpen f q (g t)).mpr
    intro y hy
    exact h ⟨t, hy.symm⟩
  · intro h y hy
    obtain ⟨t, ht⟩ := hy
    exact (mem_properFiniteFlatIsomorphismOpen f q (g t)).mp (h ⟨t, rfl⟩) y ht.symm

theorem properFiniteFlat_isIso_pullback_iff_unique_lift {T : Scheme.{u}} (g : T ⟶ B) :
    IsIso (pullback.snd f (pullback.fst q g)) ↔
      ∃! h : T ⟶ (properFiniteFlatIsomorphismOpen f q).toScheme,
        h ≫ (properFiniteFlatIsomorphismOpen f q).ι = g := by
  rw [properFiniteFlat_isIso_pullback_iff_range]
  constructor
  · intro h
    have hr : Set.range g ⊆ Set.range (properFiniteFlatIsomorphismOpen f q).ι := by
      rw [Scheme.Opens.range_ι]
      exact h
    let k := IsOpenImmersion.lift (properFiniteFlatIsomorphismOpen f q).ι g hr
    have hk : k ≫ (properFiniteFlatIsomorphismOpen f q).ι = g := IsOpenImmersion.lift_fac _ _ _
    exact ⟨k, hk, fun l hl =>
      (cancel_mono (properFiniteFlatIsomorphismOpen f q).ι).mp (hl.trans hk.symm)⟩
  · rintro ⟨h, hh, _⟩ b ⟨t, rfl⟩
    rw [← hh]
    exact (h t).property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteFlatIsomorphismLocus
