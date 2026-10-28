import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Morphism Graph Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphFamilies

noncomputable section

/-! Morphisms to separated families give faithful ideal-defined graph families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A B : Over S}

def familyGraph (p : A ⟶ B) : A ⟶ A ⊗ B := lift (𝟙 A) p

theorem familyGraph_fst (p : A ⟶ B) :
    (familyGraph p).left ≫ pullback.fst A.hom B.hom = 𝟙 A.left :=
  congrArg Over.Hom.left (lift_fst (𝟙 A) p)

theorem familyGraph_snd (p : A ⟶ B) :
    (familyGraph p).left ≫ pullback.snd A.hom B.hom = p.left :=
  congrArg Over.Hom.left (lift_snd (𝟙 A) p)

instance familyGraph_closedImmersion (p : A ⟶ B) [IsSeparated B.hom] :
    IsClosedImmersion (familyGraph p).left := by
  have : IsClosedImmersion ((familyGraph p).left ≫ pullback.fst A.hom B.hom) := by
    rw [familyGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (familyGraph p).left (pullback.fst A.hom B.hom)

def morphismGraphFamily (p : A ⟶ B) [IsSeparated B.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A.hom] : Closed.Families.FlatClosedFamily (A ⊗ B) :=
  Closed.Families.FlatClosedFamily.ofEmbedding (familyGraph p)

def morphismGraphFamilyIso (p : A ⟶ B) [IsSeparated B.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A.hom] : A ≅ (morphismGraphFamily p).scheme :=
  Closed.Families.FlatClosedFamily.ofEmbeddingIso (familyGraph p)

theorem familyGraph_eq_of_ker_eq [IsSeparated B.hom] {p q : A ⟶ B}
    (h : (familyGraph p).left.ker = (familyGraph q).left.ker) : p = q := by
  let a := IsClosedImmersion.lift (familyGraph q).left (familyGraph p).left h.symm.le
  have ha : a ≫ (familyGraph q).left = (familyGraph p).left := IsClosedImmersion.lift_fac _ _ _
  have he : a = 𝟙 A.left := by
    have hf := congrArg (fun k => k ≫ pullback.fst A.hom B.hom) ha
    rw [Category.assoc, familyGraph_fst, familyGraph_fst, Category.comp_id] at hf
    exact hf
  have hs := congrArg (fun k => k ≫ pullback.snd A.hom B.hom) ha
  rw [Category.assoc, familyGraph_snd, familyGraph_snd, he, Category.id_comp] at hs
  exact Over.OverMorphism.ext hs.symm

theorem morphismGraphFamily_injective [IsSeparated B.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A.hom] :
    Function.Injective (fun p : A ⟶ B => morphismGraphFamily p) := by
  intro p q h
  have hi := congrArg (fun F : Closed.Families.FlatClosedFamily (A ⊗ B) => F.ideal) h
  exact familyGraph_eq_of_ker_eq hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphFamilies
