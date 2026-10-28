import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Algebras
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-! # Single Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction

noncomputable section

/-!
# Completion: single-cover descent in the actual pro-étale site

A surjective quasi-compact map between site objects gives a covering sieve.
In particular, faithfully flat maps of affine site objects give actual covers,
and the sheaf condition descends compatible sections uniquely.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {X : Scheme.{u}} {U V : X.ProEt}

theorem proEtaleMorphism_weaklyEtale (f : U ⟶ V) : WeaklyEtale f.left := by
  have : WeaklyEtale (f.left ≫ V.hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  exact WeaklyEtale.of_comp f.left V.hom

/-- A surjective quasi-compact site morphism is an actual single cover. -/
theorem proEtaleSingleton_cover (f : U ⟶ V) [Surjective f.left] [QuasiCompact f.left] :
    Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology X V := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.singleton f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
    Scheme.proetalePrecoverage V.left
  rw [Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_propQCPrecoverage (f := f.left) (proEtaleMorphism_weaklyEtale f)

/-- Faithfully flat algebra maps give actual covers of their affine site objects. -/
theorem proEtaleAlgebraMap_cover {R : Type u} [CommRing R] {A B : Algebras.Construction.ProEtaleAlgebra R}
    (g : A ⟶ B) (hg : g.hom.hom.toRingHom.FaithfullyFlat) :
    Sieve.generate (Presieve.singleton ((Algebras.Construction.proEtaleAlgebraSpec R).map g.op)) ∈
      Scheme.ProEt.topology (Spec (CommRingCat.of R)) ((Algebras.Construction.proEtaleAlgebraSpec R).obj (op A)) := by
  have : Surjective ((Algebras.Construction.proEtaleAlgebraSpec R).map g.op).left :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom g.hom.hom.toRingHom)).mpr hg).2
  have : QuasiCompact ((Algebras.Construction.proEtaleAlgebraSpec R).map g.op).left := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom g.hom.hom.toRingHom))
    infer_instance
  exact proEtaleSingleton_cover _

/-- Compatible sections descend uniquely across the actual single cover. -/
theorem proEtaleSheaf_descend_section (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (f : U ⟶ V) [Surjective f.left] [QuasiCompact f.left]
    (s : F.obj.obj (op U))
    (hs : ∀ {W : X.ProEt} (p q : W ⟶ U), p ≫ f = q ≫ f →
      F.obj.map p.op s = F.obj.map q.op s) :
    ∃! t : F.obj.obj (op V), F.obj.map f.op t = s := by
  have hF : Presieve.IsSheaf (Scheme.ProEt.topology X) F.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  exact Presieve.isSheafFor_singleton.mp
    (hF.isSheafFor (Presieve.singleton f) (proEtaleSingleton_cover f)) s hs

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction
