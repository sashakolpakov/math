import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFlatOpen
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFiberFlatness

/-! # Scheme Generic Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeGenericFlatness.Construction

noncomputable section

/-! Generic flatness for finite morphisms of reduced schemes in Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- Finite generic flatness on an arbitrary nonempty reduced affine target. -/
theorem exists_nonempty_flat_source_open_of_isAffine
    {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] [IsReduced Y] [Nonempty Y]
    [IsFinite f] [LocallyOfFinitePresentation f] [Surjective f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Flat (U.ι ≫ f) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have : Nontrivial Γ(Y, ⊤) := inferInstance
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    AffineFiberFlatness.Construction.finitePresentation_module_appTop f
  have : Surjective (Spec.map f.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)).mp
      inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))) :=
    inferInstanceAs (Surjective (Spec.map f.appTop))
  obtain ⟨V, hV, hfV⟩ :=
    AffineFlatOpen.Construction.exists_nonempty_flat_source_open_affine_of_reduced Γ(Y, ⊤) Γ(X, ⊤)
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
    {X Y : Scheme} (f : X ⟶ Y) [IsReduced Y] [Nonempty Y]
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

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeGenericFlatness.Construction
