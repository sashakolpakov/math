import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.Head
import Mathlib.Algebra.Homology.Additive

/-! # Head Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadFunctor.CochainHead

noncomputable section

/-! Adjoining the first term commutes with functors preserving zero morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {W : Type w} [Category.{z} W] [HasZeroMorphisms W]
variable (F : V ⥤ W) [F.PreservesZeroMorphisms]

abbrev mapped (C : CochainComplex V ℕ) := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj C

theorem mapped_square {A : V} {C : CochainComplex V ℕ} (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) : F.map d ≫ (mapped F C).d 0 1 = 0 := by
  change F.map d ≫ F.map (C.d 0 1) = 0
  rw [← F.map_comp, h, F.map_zero]

def mapConsIso (A : V) (C : CochainComplex V ℕ) (d : A ⟶ C.X 0)
    (h : d ≫ C.d 0 1 = 0) :
    mapped F (Head.CochainHead.cons A C d h) ≅
      Head.CochainHead.cons (F.obj A) (mapped F C) (F.map d) (mapped_square F d h) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => match n with
    | 0 => Iso.refl _
    | _ + 1 => Iso.refl _) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      cases i with
      | zero =>
        simp [mapped, Head.CochainHead.cons, Head.CochainHead.consD, CochainComplex.of.d]
      | succ n =>
        simp [mapped, Head.CochainHead.cons, Head.CochainHead.consD, CochainComplex.of.d]
    )

def mapConsArrowIso {A B : V} {C D : CochainComplex V ℕ} (f : A ⟶ B) (φ : C ⟶ D)
    (d : A ⟶ C.X 0) (e : B ⟶ D.X 0)
    (hd : d ≫ C.d 0 1 = 0) (he : e ≫ D.d 0 1 = 0)
    (h : f ≫ e = d ≫ φ.f 0) :
    Arrow.mk ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (Head.CochainHead.consMap f φ d e hd he h)) ≅
      Arrow.mk (Head.CochainHead.consMap (F.map f) ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
        (F.map d) (F.map e) (mapped_square F d hd) (mapped_square F e he)
        (by change F.map f ≫ F.map e = F.map d ≫ F.map (φ.f 0)
            rw [← F.map_comp, ← F.map_comp, h])) :=
  Arrow.isoMk (mapConsIso F A C d hd) (mapConsIso F B D e he) (by
    ext n : 2
    cases n with
    | zero =>
      simp [mapConsIso, Head.CochainHead.consMap]
    | succ n =>
      simp [mapConsIso, Head.CochainHead.consMap]
  )

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.HeadFunctor.CochainHead
