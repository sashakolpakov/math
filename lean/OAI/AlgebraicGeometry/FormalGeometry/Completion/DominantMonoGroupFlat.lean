import OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoFlatOpen
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Dominant Mono Group Flat -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoGroupFlat

noncomputable section

/-! Translation extends generic flatness of a dominant group
monomorphism to all its points, also for nonreduced group schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
  [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
  (f : A ⟶ B) [IsMonHom f] [Mono f.left] [QuasiCompact f.left]
  [IsSchemeTheoreticallyDominant f.left]

theorem dominantMono_groupHom_flat : Flat f.left := by
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : Nonempty B.left := ⟨(MonObj.one (X := B)).left (IsLocalRing.closedPoint K)⟩
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [f.w]; infer_instance
    exact locallyOfFiniteType_of_comp f.left B.hom
  obtain ⟨U, hU, hflat⟩ := DominantMonoFlatOpen.Construction.dominantMono_exists_nonempty_flat_open f.left
  have : Flat (U.ι ≫ f.left) := hflat
  exact FlatTranslation.Construction.flat_of_transitive_automorphisms f.left (Finite.GroupHomFlat.Construction.groupHom_transitive_automorphisms f) U hU

theorem dominantMono_groupHom_isOpenImmersion : IsOpenImmersion f.left := by
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [f.w]; infer_instance
    exact locallyOfFiniteType_of_comp f.left B.hom
  have : Flat f.left := dominantMono_groupHom_flat f
  exact IsOpenImmersion.of_flat_of_mono f.left

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantMonoGroupFlat
