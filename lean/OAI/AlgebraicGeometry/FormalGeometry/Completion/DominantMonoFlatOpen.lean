import OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoArtinianStalk
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ArtinianGenericStalk
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonoOpenSection

/-! # Dominant Mono Flat Open -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoFlatOpen

noncomputable section

/-! Every finite-type scheme-theoretically dominant monomorphism over
a nonempty locally Noetherian target is flat on a nonempty source open. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem dominantMono_exists_nonempty_flat_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Mono f] [LocallyOfFiniteType f] [QuasiCompact f] [IsSchemeTheoreticallyDominant f]
    [IsLocallyNoetherian Y] [Nonempty Y] :
    ∃ V : X.Opens, (V : Set X).Nonempty ∧ Flat (V.ι ≫ f) := by
  obtain ⟨y, hy⟩ := ArtinianGenericStalk.Construction.exists_artinian_stalk Y
  have : IsArtinianRing (Y.presheaf.stalk y) := hy
  obtain ⟨U, hyU, j, hj⟩ := DominantMonoArtinianStalk.Construction.dominantMono_hasLocalSection f y
  have : IsOpenImmersion j := MonoOpenSection.Construction.monoOpenSection_isOpenImmersion f U j hj
  have : Flat (j ≫ f) := by rw [hj]; infer_instance
  refine ⟨j.opensRange, ⟨j ⟨y, hyU⟩, ⟨⟨y, hyU⟩, rfl⟩⟩, ?_⟩
  rw [← j.isoOpensRange_inv_comp, Category.assoc]
  infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoFlatOpen
