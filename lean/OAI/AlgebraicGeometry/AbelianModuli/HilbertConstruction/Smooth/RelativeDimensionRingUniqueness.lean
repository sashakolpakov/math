import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialBasicLocalization
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Relative Dimension Ring Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeDimensionRingUniqueness

noncomputable section

/-! Standard smooth relative dimension, and its target-local form, are unique for a nonzero target ring. -/

universe u

theorem standardSmoothRelativeDimension_unique {R B : Type u} [CommRing R] [CommRing B] [Nontrivial B]
    (f : R →+* B) (n m : ℕ) (hn : f.IsStandardSmoothOfRelativeDimension n)
    (hm : f.IsStandardSmoothOfRelativeDimension m) : n = m := by
  let : Algebra R B := f.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n R B := hn
  let : Algebra.IsStandardSmoothOfRelativeDimension m R B := hm
  have h := (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := B) n).symm.trans
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := B) m)
  exact_mod_cast h

theorem locallyStandardSmoothRelativeDimension_unique {R B : Type u} [CommRing R] [CommRing B] [Nontrivial B]
    (f : R →+* B) (n m : ℕ) (hn : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f)
    (hm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m) f) : n = m := by
  obtain ⟨s, hs, hn⟩ := hn
  obtain ⟨r, hr, hBr⟩ := NontrivialBasicLocalization.exists_nontrivial_away_of_span_top B s hs
  let : Nontrivial (Localization.Away r) := hBr
  let fr := (algebraMap B (Localization.Away r)).comp f
  have hmr : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m) fr :=
    (RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).right)
      (Localization.Away r) r f hm
  obtain ⟨t, ht, hmt⟩ := hmr
  obtain ⟨z, hz, hBz⟩ := NontrivialBasicLocalization.exists_nontrivial_away_of_span_top (Localization.Away r) t ht
  let : Nontrivial (Localization.Away z) := hBz
  have hnz : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap (Localization.Away r) (Localization.Away z)).comp fr) :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (Localization.Away z) z fr (hn r hr)
  exact standardSmoothRelativeDimension_unique _ n m hnz (hmt z hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeDimensionRingUniqueness
