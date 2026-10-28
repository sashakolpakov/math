/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCochainSections

/-! # Represented Cochain Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCochainNaturality.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def homComplexPostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    ((CochainComplex.singleFunctor C 0).obj Z).HomComplex K ⟶
      ((CochainComplex.singleFunctor C 0).obj Z).HomComplex L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.comp (.ofHom f) (add_zero n)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  comm' i j _ := by
    ext z
    exact CochainComplex.HomComplex.δ_comp_ofHom z f j

lemma homComplexPostcomp_f_apply {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    ((homComplexPostcomp f).f n).hom z =
      z.comp (.ofHom f) (add_zero n) :=
  rfl

lemma homComplexIsoSections_naturality
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    homComplexPostcomp f ≫ (RepresentedCochainSections.DerivedSections.homComplexIsoSections e he L).hom =
      (RepresentedCochainSections.DerivedSections.homComplexIsoSections e he K).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map f := by
  ext n z
  obtain ⟨a, rfl⟩ :=
    CochainComplex.HomComplex.Cochain.fromSingleMk_surjective z n (zero_add n)
  let α := CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)
  have hleft :
      ((((homComplexPostcomp f ≫
          (RepresentedCochainSections.DerivedSections.homComplexIsoSections e he L).hom).f n).hom α) =
        e (L.X n) (a ≫ f.f n)) := by
    rw [HomologicalComplex.comp_f]
    change ((RepresentedCochainSections.DerivedSections.homComplexIsoSections e he L).hom.f n).hom
      (((homComplexPostcomp f).f n).hom α) = _
    change RepresentedCochainSections.DerivedSections.cochainToSectionsEquiv e L n
      (α.comp (.ofHom f) (add_zero n)) = _
    rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp]
    exact RepresentedCochainSections.DerivedSections.cochainToSectionsEquiv_fromSingleMk e L n (a ≫ f.f n)
  have hright :
      (((((RepresentedCochainSections.DerivedSections.homComplexIsoSections e he K).hom ≫
          (G.mapHomologicalComplex (.up ℤ)).map f).f n).hom α) =
        (G.map (f.f n)).hom (e (K.X n) a)) := by
    rw [HomologicalComplex.comp_f]
    change (((G.mapHomologicalComplex (.up ℤ)).map f).f n).hom
      (((RepresentedCochainSections.DerivedSections.homComplexIsoSections e he K).hom.f n).hom α) = _
    rw [Functor.mapHomologicalComplex_map_f]
    change (G.map (f.f n)).hom (RepresentedCochainSections.DerivedSections.cochainToSectionsEquiv e K n α) = _
    exact congrArg (G.map (f.f n)).hom
      (RepresentedCochainSections.DerivedSections.cochainToSectionsEquiv_fromSingleMk e K n a)
  exact hleft.trans ((he a (f.f n)).trans hright.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCochainNaturality.DerivedSections
