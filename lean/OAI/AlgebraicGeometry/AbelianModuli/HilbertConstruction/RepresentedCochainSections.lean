/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology

/-! # Represented Cochain Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCochainSections.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def cochainToSectionsEquiv
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain
        ((CochainComplex.singleFunctor C 0).obj Z) K n ≃+
      ↑(G.obj (K.X n)) :=
  (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans (e (K.X n))

def cochainToSectionsIso
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) :
    (((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).X n ≅
      ((G.mapHomologicalComplex (.up ℤ)).obj K).X n :=
  (cochainToSectionsEquiv e K n).toAddCommGrpIso

omit [G.Additive] in
lemma cochainToSectionsEquiv_fromSingleMk
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) (f : Z ⟶ K.X n) :
    cochainToSectionsEquiv e K n
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add n)) = e (K.X n) f := by
  exact congrArg (e (K.X n))
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk f (zero_add n))

lemma cochainToSectionsIso_hom_apply
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    (cochainToSectionsIso e K n).hom.hom α = cochainToSectionsEquiv e K n α :=
  rfl

lemma homComplex_d_apply
    (K : CochainComplex C ℤ) (i j : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K i) :
    ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).d i j).hom α =
      CochainComplex.HomComplex.δ i j α :=
  rfl

def homComplexIsoSections
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f))
    (K : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj Z).HomComplex K ≅
      (G.mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (cochainToSectionsIso e K) fun i j hij ↦ by
    ext α
    obtain ⟨f, rfl⟩ :=
      CochainComplex.HomComplex.Cochain.fromSingleMk_surjective α i (zero_add i)
    let α := CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add i)
    have hleft :
        (((cochainToSectionsIso e K i).hom ≫
            ((G.mapHomologicalComplex (.up ℤ)).obj K).d i j).hom α) =
          (G.map (K.d i j)).hom (e (K.X i) f) := by
      change (((G.mapHomologicalComplex (.up ℤ)).obj K).d i j).hom
        ((cochainToSectionsIso e K i).hom.hom α) = _
      rw [Functor.mapHomologicalComplex_obj_d]
      rw [cochainToSectionsIso_hom_apply]
      exact congrArg (G.map (K.d i j)).hom
        (cochainToSectionsEquiv_fromSingleMk e K i f)
    have hright :
        (((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).d i j ≫
            (cochainToSectionsIso e K j).hom).hom α) =
          e (K.X j) (f ≫ K.d i j) := by
      change (cochainToSectionsIso e K j).hom.hom
        (((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).d i j).hom α) = _
      change cochainToSectionsEquiv e K j
        (CochainComplex.HomComplex.δ i j α) = _
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i) j j
        (zero_add j)]
      exact cochainToSectionsEquiv_fromSingleMk e K j (f ≫ K.d i j)
    exact hleft.trans ((he f (K.d i j)).symm.trans hright.symm)

lemma homComplexIsoSections_hom_f_apply
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    (K : CochainComplex C ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    ((homComplexIsoSections e he K).hom.f n).hom z =
      cochainToSectionsEquiv e K n z :=
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCochainSections.DerivedSections
