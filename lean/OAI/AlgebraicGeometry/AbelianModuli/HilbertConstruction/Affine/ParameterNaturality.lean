import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterNaturality

/-! # Parameter Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterNaturality

noncomputable section

/-! Quotient classification is natural for arbitrary morphisms between affine test spectra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {S : Scheme.{u}} (A B : CommRingCat.{u}) (f : Spec A ⟶ S) (g : Spec B ⟶ S)
variable (x : Over.mk g ⟶ Over.mk f)

def affineTestCoefficientMap : A →+* B :=
  (Spec.fullyFaithful.preimage x.left).unop.hom

theorem affineTestCoefficientMap_spec :
    Spec.map (CommRingCat.ofHom (affineTestCoefficientMap A B f g x)) = x.left :=
  Spec.fullyFaithful.map_preimage x.left

theorem affineTestCoefficientMap_sections (a : A) :
    x.left.appTop ((Scheme.ΓSpecIso A).inv a) =
      (Scheme.ΓSpecIso B).inv (affineTestCoefficientMap A B f g x a) := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (affineTestCoefficientMap A B f g x))
  rw [affineTestCoefficientMap_spec] at h
  exact (ConcreteCategory.congr_hom h a).symm

theorem affineTestCoefficientMap_matrix {α β : Type*} (F : Matrix α β A) :
    (F.map (Scheme.ΓSpecIso A).inv.hom).map x.left.appTop.hom =
      (F.map (affineTestCoefficientMap A B f g x)).map (Scheme.ΓSpecIso B).inv.hom := by
  ext i j
  exact affineTestCoefficientMap_sections A B f g x (F i j)

theorem grassmannParameterAffine_naturality
    (N : Module.Grassmannian A (ν → A) (Fintype.card ι)) :
    Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv B g
      (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap (affineTestCoefficientMap A B f g x) N) =
        x ≫ Grassmann.ParameterScheme.grassmannParameterAffinePointEquiv A f N := by
  apply Over.OverMorphism.ext
  have h := Grassmann.ParameterNaturality.grassmannParameterAffinePointEquiv_naturality A B
    (affineTestCoefficientMap A B f g x) f N
  have hx : x.left ≫ f = g := x.w
  rw [affineTestCoefficientMap_spec, hx] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterNaturality
