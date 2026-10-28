import OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.SpreadingOut

/-! # Dominant Mono Artinian Stalk -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoArtinianStalk

noncomputable section

/-! A scheme-theoretically dominant monomorphism is an isomorphism
over an Artinian stalk. Its inverse spreads to an actual open neighborhood. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSchemeTheoreticallyDominant f]

theorem dominantMono_artinianStalk_isIso (y : Y) [IsArtinianRing (Y.presheaf.stalk y)] :
    IsIso (pullback.snd f (Y.fromSpecStalk y)) := by
  have : Flat (Y.fromSpecStalk y) := StalkFlat.Construction.scheme_fromSpecStalk_flat Y y
  have : IsFinite (pullback.snd f (Y.fromSpecStalk y)) :=
    IsFinite.of_locallyQuasiFinite _
  have : IsClosedImmersion (pullback.snd f (Y.fromSpecStalk y)) :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (Scheme.Hom.ker_eq_bot _)

theorem dominantMono_artinianStalk_hasLift (y : Y) [IsArtinianRing (Y.presheaf.stalk y)] :
    ∃ φ : Spec (Y.presheaf.stalk y) ⟶ X, φ ≫ f = Y.fromSpecStalk y := by
  have := dominantMono_artinianStalk_isIso f y
  refine ⟨inv (pullback.snd f (Y.fromSpecStalk y)) ≫ pullback.fst f (Y.fromSpecStalk y), ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

theorem dominantMono_hasLocalSection [IsLocallyNoetherian Y]
    (y : Y) [IsArtinianRing (Y.presheaf.stalk y)] :
    ∃ (U : Y.Opens), y ∈ U ∧ ∃ j : U.toScheme ⟶ X, j ≫ f = U.ι := by
  obtain ⟨φ, hφ⟩ := dominantMono_artinianStalk_hasLift f y
  obtain ⟨U, hy, j, _, hj⟩ := spread_out_of_isGermInjective' (𝟙 Y) f φ (by simpa using hφ)
  exact ⟨U, hy, j, by simpa using hj⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoArtinianStalk
