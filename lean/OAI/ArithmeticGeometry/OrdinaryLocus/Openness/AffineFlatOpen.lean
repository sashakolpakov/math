import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations

/-! # Affine Flat Open -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFlatOpen.Construction

noncomputable section

/-! Affine generic flatness as an actual nonempty source open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

/-- A surjective affine morphism with finite-presentation algebra module over
a nonzero reduced base is flat on some nonempty source open. -/
theorem exists_nonempty_flat_source_open_affine_of_reduced
    (R B : Type u) [CommRing R] [_root_.IsReduced R] [Nontrivial R]
    [CommRing B] [Algebra R B]
    [Module.FinitePresentation R B]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))] :
    ∃ U : (Spec (.of B)).Opens, (U : Set (Spec (.of B))).Nonempty ∧
      Flat (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  obtain ⟨r, hnontriv, hflat⟩ := GenericFlatness.Construction.exists_nontrivial_flat_affine_baseChange_of_reduced R B
  let Rr := Localization.Away r
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let i := Spec.map (CommRingCat.ofHom (algebraMap R Rr))
  let j := pullback.snd i f
  have : IsOpenImmersion i := by
    dsimp [i, Rr]
    infer_instance
  have : IsOpenImmersion j := by
    dsimp [j]
    infer_instance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap Rr (Rr ⊗[R] B)))) := hflat
  have : Flat (pullback.fst i f) := by
    rw [← pullbackSpecIso_hom_fst' R Rr B]
    infer_instance
  have : Flat (j ≫ f) := by
    change Flat (pullback.snd i f ≫ f)
    rw [← pullback.condition]
    infer_instance
  have : Nontrivial Rr := hnontriv
  have : Surjective (pullback.fst i f) := by
    dsimp [f]
    infer_instance
  have : Nonempty ↥(pullback i f) :=
    (pullback.fst i f).surjective.nonempty
  refine ⟨j.opensRange, ?_, ?_⟩
  · obtain ⟨z⟩ := ‹Nonempty ↥(pullback i f)›
    exact ⟨j z, ⟨z, rfl⟩⟩
  · rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

/-- The integral-base form of generic flatness for an affine morphism. -/
theorem exists_nonempty_flat_source_open_affine
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Module.FinitePresentation R B]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))] :
    ∃ U : (Spec (.of B)).Opens, (U : Set (Spec (.of B))).Nonempty ∧
      Flat (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  exists_nonempty_flat_source_open_affine_of_reduced R B

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFlatOpen.Construction
