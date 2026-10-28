import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Flat Cartier Embedding Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatCartierEmbeddingIso.Construction

noncomputable section

/-! A finite flat subfunctor of a finite etale scheme is etale.
Surjectivity on geometric points then makes its embedding an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem surjective_of_geometric_sections
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      Function.Surjective (fun x : Over.mk s ⟶ X => x ≫ f)) : Surjective f.left := by
  constructor
  intro y
  let k := AlgebraicClosure (Y.left.residueField y)
  let a := Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) k)) ≫
    Y.left.fromSpecResidueField y
  let s := a ≫ Y.hom
  let z : Over.mk s ⟶ Y := Over.homMk a rfl
  obtain ⟨x, hx⟩ := h k s z
  let t : Spec (.of k) := default
  refine ⟨x.left t, ?_⟩
  have he := congrArg (fun m : Over.mk s ⟶ Y => m.left t) hx
  exact he.trans (Y.left.fromSpecResidueField_apply y _)

theorem finiteFlatEmbedding_etale
    {S : Scheme.{u}} {X Y : Over S}
    [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom] [Etale Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [Mono f] : Etale f.left := by
  have : IsFinite (f.left ≫ Y.hom) := f.w.symm ▸ inferInstanceAs (IsFinite X.hom)
  have : IsFinite f.left := IsFinite.of_comp f.left Y.hom
  have : Mono f.left := inferInstanceAs (Mono ((Over.forget S).map f))
  have : IsClosedImmersion f.left :=
    (IsClosedImmersion.iff_isFinite_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩
  have : FormallyUnramified f.left := inferInstance
  have : FormallyUnramified X.hom := by
    rw [← f.w]
    exact MorphismProperty.comp_mem @FormallyUnramified f.left Y.hom inferInstance inferInstance
  have : Etale X.hom := Etale.of_formallyUnramified_of_flat X.hom
  have : Etale (f.left ≫ Y.hom) := f.w.symm ▸ inferInstanceAs (Etale X.hom)
  exact Etale.of_comp f.left Y.hom

theorem finiteFlatEmbedding_isIso_of_geometric_surjective
    {S : Scheme.{u}} {X Y : Over S}
    [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom] [Etale Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [Mono f]
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      Function.Surjective (fun x : Over.mk s ⟶ X => x ≫ f)) : IsIso f := by
  have : Etale f.left := finiteFlatEmbedding_etale f
  have : Surjective f.left := surjective_of_geometric_sections f h
  have : Mono f.left := inferInstanceAs (Mono ((Over.forget S).map f))
  have : IsOpenImmersion f.left := IsOpenImmersion.of_flat_of_mono f.left
  have : IsIso f.left := (isIso_iff_isOpenImmersion_and_surjective f.left).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget S).map f) := inferInstanceAs (IsIso f.left)
  exact isIso_of_reflects_iso f (Over.forget S)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatCartierEmbeddingIso.Construction
