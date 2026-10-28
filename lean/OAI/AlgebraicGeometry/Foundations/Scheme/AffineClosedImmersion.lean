import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Affine Closed Immersion -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion

noncomputable section

/-!
# Affine equations of a closed immersion

A closed immersion into an affine scheme has affine source. Its coordinate ring
is the quotient of the target coordinate ring by the actual kernel ideal.
The resulting spectrum isomorphism is compatible with the original immersion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

variable {X Y : Scheme.{u}} [IsAffine Y] (i : X ⟶ Y) [IsClosedImmersion i]

include i in
/-- A closed subscheme of an affine scheme is affine. -/
theorem affineClosedImmersion_source_isAffine : IsAffine X :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).1

/-- The coordinate map of a closed immersion into an affine scheme is surjective. -/
theorem affineClosedImmersion_appTop_surjective : Function.Surjective i.appTop :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- The actual ideal of equations in the target's coordinate ring. -/
abbrev affineClosedImmersionIdeal : Ideal Γ(Y, ⊤) := RingHom.ker i.appTop.hom

/-- The source coordinate ring is the quotient by the actual ideal of equations. -/
def affineClosedImmersionCoordinateEquiv :
    (Γ(Y, ⊤) ⧸ affineClosedImmersionIdeal i) ≃+* Γ(X, ⊤) :=
  RingHom.quotientKerEquivOfSurjective (affineClosedImmersion_appTop_surjective i)

@[simp]
theorem affineClosedImmersionCoordinateEquiv_mk (a : Γ(Y, ⊤)) :
    affineClosedImmersionCoordinateEquiv i
      (Ideal.Quotient.mk (affineClosedImmersionIdeal i) a) = i.appTop a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ a

/-- The affine closed subscheme is the actual spectrum of its quotient ring. -/
def affineClosedImmersionIsoQuotient :
    X ≅ Spec (.of (Γ(Y, ⊤) ⧸ affineClosedImmersionIdeal i)) := by
  letI : IsAffine X := affineClosedImmersion_source_isAffine i
  exact X.isoSpec ≪≫ Scheme.Spec.mapIso
    (affineClosedImmersionCoordinateEquiv i).toCommRingCatIso.op

/-- The quotient ring map agrees with the original map on global sections. -/
theorem affineClosedImmersion_quotient_comp :
    CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionIdeal i)) ≫
      (affineClosedImmersionCoordinateEquiv i).toCommRingCatIso.hom = i.appTop := by
  ext a
  exact affineClosedImmersionCoordinateEquiv_mk i a

/-- The spectrum isomorphism carries the original immersion to the quotient map. -/
theorem affineClosedImmersionIsoQuotient_over :
    (affineClosedImmersionIsoQuotient i).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (affineClosedImmersionIdeal i))) ≫
      Y.isoSpec.inv = i := by
  let _ : IsAffine X := affineClosedImmersion_source_isAffine i
  simp only [affineClosedImmersionIsoQuotient, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
  rw [← Category.assoc (Spec.map _) (Spec.map _) Y.isoSpec.inv,
    ← Spec.map_comp, affineClosedImmersion_quotient_comp]
  rw [Scheme.isoSpec_inv_naturality]
  simp

/-- A ring map whose spectrum morphism is a closed immersion is surjective. -/
theorem ringMap_surjective_of_spec_closedImmersion {R S : CommRingCat.{u}}
    (f : R ⟶ S) [IsClosedImmersion (Spec.map f)] : Function.Surjective f := by
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2
  have hcomp : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫
      (Scheme.ΓSpecIso S).hom = f := by simp
  rw [← hcomp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).2.comp hs).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2

/-- For algebra maps, the coordinate quotient identification respects the base
algebra structure, in particular for complex algebras. -/
def algebraQuotientEquivOfSpecClosedImmersion {K : Type v} [CommRing K]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    (A ⧸ RingHom.ker f) ≃ₐ[K] B :=
  Ideal.quotientKerAlgEquivOfSurjective
    (ringMap_surjective_of_spec_closedImmersion (CommRingCat.ofHom f.toRingHom))

@[simp]
theorem algebraQuotientEquivOfSpecClosedImmersion_mk {K : Type v} [CommRing K]
    {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] (a : A) :
    algebraQuotientEquivOfSpecClosedImmersion f (Ideal.Quotient.mk (RingHom.ker f) a) =
      f a := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion
