import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductCoverFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalProductMap
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalSetup
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFiber

/-! # Normalized Product Cover Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedProductCoverFunctions.Construction

noncomputable section

/-! Formal functions and actual connected fibers for normalized finite etale product covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A B T : Scheme.{u}}
  [IsIntegral A] [IsIntegral B]
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
  (t : T ⟶ pullback p q) [IsFinite t] [Etale t]
  (n : (t ≫ pullback.snd p q).normalization)

/-- Actual normalized local formal functions, with the global-section isomorphism and
projective detecting cover derived from the original finite etale product geometry. -/
theorem finiteEtaleProductCover_normalizedLocalFormalComparison_surjective :
    ComparisonProperty.Construction.NormalizedLocalFormalComparisonSurjective (t ≫ pullback.snd p q) n := by
  let f := t ≫ pullback.snd p q
  have : IsProper f := inferInstanceAs (IsProper (t ≫ pullback.snd p q))
  have : Smooth f := inferInstanceAs (Smooth (t ≫ pullback.snd p q))
  obtain ⟨hfin, het⟩ := Proper.SmoothFiniteEtaleNormalization.Construction.proper_smooth_family_normalization_finite_etale K (f ≫ q) q f
  have : IsFinite (t ≫ pullback.snd p q).fromNormalization := hfin
  have : Etale (t ≫ pullback.snd p q).fromNormalization := het
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have : IsNoetherianRing (f.normalization.presheaf.stalk n) := inferInstance
  let a := NormalizedLocalProductMap.Construction.normalizedLocalProductMap p q t n
  let b := NormalizedLocalProductMap.Construction.normalizedLocalBaseToField p q t n
  have : IsFinite a := NormalizedLocalProductMap.Construction.normalizedLocalProductMap_finite p q t n
  have : Etale a := NormalizedLocalProductMap.Construction.normalizedLocalProductMap_etale p q t n
  have hb : a ≫ pullback.snd p b = NormalizedLocalFunctions.Construction.normalizedLocalFamily f n := NormalizedLocalProductMap.Construction.normalizedLocalProductMap_snd p q t n
  have : IsIso (a ≫ pullback.snd p b).appTop := by
    rw [hb]
    exact NormalizedLocalFunctions.Construction.normalizedLocalFamily_appTop_isIso f n
  have hA (x : A) : IsIntegrallyClosed (A.presheaf.stalk x) := by
    have := Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk p x
    infer_instance
  have h := Proper.ProductCoverFunctions.Construction.properProductCover_formalFunctionsComparisonSurjective
    (R := f.normalization.presheaf.stalk n) p b a hA
    (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n))
  rw [hb] at h
  exact h

/-- Connectedness follows from the actual nontrivial infinitesimal idempotent obstruction. -/
theorem finiteEtaleProductCover_normalizedLocal_infinitesimal_connected :
    ConnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood
      (IsLocalRing.maximalIdeal ((t ≫ pullback.snd p q).normalization.presheaf.stalk n))
      (NormalizedLocalFunctions.Construction.normalizedLocalFamily (t ≫ pullback.snd p q) n) 0) := by
  let f := t ≫ pullback.snd p q
  have : IsProper f := inferInstanceAs (IsProper (t ≫ pullback.snd p q))
  have : Smooth f := inferInstanceAs (Smooth (t ≫ pullback.snd p q))
  obtain ⟨hR, _hp, _hs, hsurj, _hΓ⟩ := NormalizedLocalSetup.Construction.proper_smooth_normalizedLocalFamily_properties K
    (f ≫ q) q f n
  have : IsNoetherianRing (f.normalization.presheaf.stalk n) := hR
  exact ComparisonProperty.Construction.normalizedLocal_initial_connected_of_formal_surjective f n hsurj
    (finiteEtaleProductCover_normalizedLocalFormalComparison_surjective p q t n)

/-- The actual scheme-theoretic fibers of the first normalization factor are connected. -/
theorem finiteEtaleProductCover_normalized_fiber_connected :
    ConnectedSpace ((t ≫ pullback.snd p q).toNormalization.fiber n) := by
  have := finiteEtaleProductCover_normalizedLocal_infinitesimal_connected p q t n
  exact NormalizedLocalFiber.Construction.normalized_fiber_connected_of_local_initial_connected (t ≫ pullback.snd p q) n

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedProductCoverFunctions.Construction
