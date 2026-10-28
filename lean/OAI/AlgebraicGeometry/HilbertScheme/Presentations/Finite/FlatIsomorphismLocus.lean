import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Flat Isomorphism Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FlatIsomorphismLocus

noncomputable section

/-! The rank-one open of a finite flat finitely presented morphism
represents its isomorphism condition under every scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

def finiteFlatIsomorphismOpen : Y.Opens :=
  ⟨{y | f.finrank y = 1}, f.isLocallyConstant_finrank.isOpen_fiber 1⟩

theorem finiteFlatIsomorphismOpen_isClopen :
    IsClopen (finiteFlatIsomorphismOpen f : Set Y) :=
  f.isLocallyConstant_finrank.isClopen_fiber 1

theorem finiteFlat_isIso_pullback_iff_range {T : Scheme.{u}} (g : T ⟶ Y) :
    IsIso (pullback.snd f g) ↔ Set.range g ⊆ (finiteFlatIsomorphismOpen f : Set Y) := by
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  constructor
  · intro h y hy
    obtain ⟨t, rfl⟩ := hy
    change f.finrank (g t) = 1
    rw [← Scheme.Hom.finrank_pullback_snd f g t]
    exact congrFun h t
  · intro h
    funext t
    change (pullback.snd f g).finrank t = 1
    rw [Scheme.Hom.finrank_pullback_snd]
    exact h ⟨t, rfl⟩

theorem finiteFlat_isIso_pullback_iff_unique_lift {T : Scheme.{u}} (g : T ⟶ Y) :
    IsIso (pullback.snd f g) ↔
      ∃! h : T ⟶ (finiteFlatIsomorphismOpen f).toScheme,
        h ≫ (finiteFlatIsomorphismOpen f).ι = g := by
  rw [finiteFlat_isIso_pullback_iff_range]
  constructor
  · intro h
    have hr : Set.range g ⊆ Set.range (finiteFlatIsomorphismOpen f).ι := by
      rw [Scheme.Opens.range_ι]
      exact h
    let k := IsOpenImmersion.lift (finiteFlatIsomorphismOpen f).ι g hr
    have hk : k ≫ (finiteFlatIsomorphismOpen f).ι = g := IsOpenImmersion.lift_fac _ _ _
    exact ⟨k, hk, fun l hl => (cancel_mono (finiteFlatIsomorphismOpen f).ι).mp (hl.trans hk.symm)⟩
  · rintro ⟨h, hh, _⟩ y ⟨t, rfl⟩
    rw [← hh]
    exact (h t).property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FlatIsomorphismLocus
