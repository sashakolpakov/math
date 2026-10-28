import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Generic Flatness -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GenericFlatness.Construction

noncomputable section

/-! Actual nonempty flat opens for finite morphisms.
The local and scheme arguments are adapted from AffineFlatOpen,
AffineFiberFlatness, and SchemeGenericFlatness with explicit universes.
Only the standalone, audited generic-freeness module is imported. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

/-- A finite, locally finitely presented affine morphism gives a finitely
presented module on global sections. -/
theorem finitePresentation_module_appTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [IsFinite f] [LocallyOfFinitePresentation f] :
    let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := f.finitePresentation_appTop
  exact Module.FinitePresentation.of_finite_of_finitePresentation _ _

/-- A surjective affine morphism with finite-presentation algebra module over
a nonzero reduced base is flat on some nonempty source open. -/
theorem exists_nonempty_flat_source_open_affine_of_reduced
    (R B : Type u) [CommRing R] [_root_.IsReduced R] [Nontrivial R]
    [CommRing B] [Algebra R B]
    [Module.FinitePresentation R B]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))] :
    ∃ U : (Spec (.of B)).Opens, (U : Set (Spec (.of B))).Nonempty ∧
      Flat (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  obtain ⟨r, hnontriv, hflat⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness.Construction.exists_nontrivial_flat_affine_baseChange_of_reduced R B
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

/-- Finite generic flatness on an arbitrary nonempty reduced affine target. -/
theorem exists_nonempty_flat_source_open_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsReduced Y] [Nonempty Y]
    [IsFinite f] [LocallyOfFinitePresentation f] [Surjective f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Flat (U.ι ≫ f) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have : Nontrivial Γ(Y, ⊤) := inferInstance
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    finitePresentation_module_appTop f
  have : Surjective (Spec.map f.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)).mp
      inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))) :=
    inferInstanceAs (Surjective (Spec.map f.appTop))
  obtain ⟨V, hV, hfV⟩ :=
    exists_nonempty_flat_source_open_affine_of_reduced Γ(Y, ⊤) Γ(X, ⊤)
  have : Flat (V.ι ≫ Spec.map f.appTop) := hfV
  let j := V.ι ≫ X.isoSpec.inv
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have : Flat (j ≫ f) := by
    dsimp [j]
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc]
    infer_instance
  refine ⟨j.opensRange, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hV
    exact ⟨j ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
  · rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

/-- A finite surjective morphism of finite presentation over a nonempty
reduced scheme is flat on a nonempty open subset of its source. -/
theorem exists_nonempty_flat_source_open_of_reduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced Y] [Nonempty Y]
    [IsFinite f] [LocallyOfFinitePresentation f] [Surjective f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Flat (U.ι ≫ f) := by
  let y : Y := Classical.choice inferInstance
  let i := Y.affineCover.idx y
  let g := Y.affineCover.f i
  have : Nonempty (Y.affineCover.X i) := by
    obtain ⟨z, _⟩ := Y.affineCover.covers y
    exact ⟨z⟩
  let f' := pullback.snd f g
  have : IsReduced (Y.affineCover.X i) := inferInstance
  obtain ⟨V, hV, hfV⟩ := exists_nonempty_flat_source_open_of_isAffine f'
  let j := V.ι ≫ pullback.fst f g
  have : IsOpenImmersion j := by dsimp [j, g]; infer_instance
  have : Flat (V.ι ≫ f') := hfV
  have : Flat (j ≫ f) := by
    dsimp [j]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change Flat ((V.ι ≫ f') ≫ g)
    infer_instance
  refine ⟨j.opensRange, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hV
    exact ⟨j ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
  · rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GenericFlatness.Construction
