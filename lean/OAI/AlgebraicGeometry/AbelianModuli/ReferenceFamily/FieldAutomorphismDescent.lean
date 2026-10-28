import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldEndomorphismDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Field Automorphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldAutomorphismDescent.FieldDescent

noncomputable section

/-! Actual group automorphisms descend across extensions of an
algebraically closed field. Their inverse identities descend by faithful
flat pullback, so invertibility is constructed over the ground field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (k B : Type) [Field k] [IsAlgClosed k] [Field B] [Algebra k B]
  {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

omit [IsAlgClosed k] in
theorem fieldBaseChange_faithful :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Faithful := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    ⟨Function.surjective_to_subsingleton _⟩
  infer_instance

theorem field_group_automorphism_descends
    (e : (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).scheme ≅
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).scheme)
    [IsMonHom e.hom] :
    ∃ d : A.scheme ≅ A.scheme, IsMonHom d.hom ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).map d.hom = e.hom := by
  obtain ⟨f, hf, he⟩ := FieldEndomorphismDescent.FieldDescent.field_endomorphism_descends k B A e.hom
  obtain ⟨j, hj, he'⟩ := FieldEndomorphismDescent.FieldDescent.field_endomorphism_descends k B A e.inv
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  have : F.Faithful := fieldBaseChange_faithful k B
  have hfj : f ≫ j = 𝟙 A.scheme := by
    apply F.map_injective
    simp only [Functor.map_comp]
    exact (congrArg₂ (fun u v => u ≫ v) he he').trans
      (e.hom_inv_id.trans (F.map_id A.scheme).symm)
  have hjf : j ≫ f = 𝟙 A.scheme := by
    apply F.map_injective
    simp only [Functor.map_comp]
    exact (congrArg₂ (fun u v => u ≫ v) he' he).trans
      (e.inv_hom_id.trans (F.map_id A.scheme).symm)
  exact ⟨⟨f, j, hfj, hjf⟩, hf, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldAutomorphismDescent.FieldDescent
