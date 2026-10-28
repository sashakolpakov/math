import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelAlgebraNaturality
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Base Algebra Points -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints

noncomputable section

/-! Algebra maps into actual global functions classify morphisms to the
spectrum of an algebra over an affine scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite

namespace Construction

universe u

def globalRingPointEquiv (X : Scheme.{u}) (B : CommRingCat.{u}) :
    (X ⟶ Spec B) ≃ (B →+* Γ(X, ⊤)) where
  toFun f := (((ΓSpec.adjunction).homEquiv X (op B)).symm f).unop.hom
  invFun φ := (ΓSpec.adjunction).homEquiv X (op B) (CommRingCat.ofHom φ).op
  left_inv f := ((ΓSpec.adjunction).homEquiv X (op B)).apply_symm_apply f
  right_inv φ := congrArg (fun h => h.unop.hom)
    (((ΓSpec.adjunction).homEquiv X (op B)).symm_apply_apply (CommRingCat.ofHom φ).op)

theorem globalRingPointEquiv_apply (X : Scheme.{u}) (B : CommRingCat.{u}) (f : X ⟶ Spec B) (b : B) :
    globalRingPointEquiv X B f b = f.appTop ((Scheme.ΓSpecIso B).inv b) := rfl

theorem globalRingPointEquiv_source {X Y : Scheme.{u}} (B : CommRingCat.{u})
    (f : X ⟶ Y) (p : Y ⟶ Spec B) :
    globalRingPointEquiv X B (f ≫ p) = f.appTop.hom.comp (globalRingPointEquiv Y B p) :=
  congrArg (fun h => h.unop.hom) ((ΓSpec.adjunction).homEquiv_naturality_left_symm f p)

theorem globalRingPointEquiv_target (X : Scheme.{u}) {B R : CommRingCat.{u}}
    (a : R ⟶ B) (p : X ⟶ Spec B) :
    globalRingPointEquiv X R (p ≫ Spec.map a) = (globalRingPointEquiv X B p).comp a.hom :=
  congrArg (fun h => h.unop.hom) ((ΓSpec.adjunction).homEquiv_naturality_right_symm p a.op)

theorem globalRingPointEquiv_toSpecΓ (X : Scheme.{u}) :
    globalRingPointEquiv X Γ(X, ⊤) X.toSpecΓ = RingHom.id Γ(X, ⊤) := by
  apply RingHom.ext
  intro x
  rw [globalRingPointEquiv_apply, Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) (Scheme.ΓSpecIso Γ(X, ⊤)) x

variable (S : Scheme.{u}) [IsAffine S] (B : CommAlgCat.{u} Γ(S, ⊤))

def affineBaseAlgebraMap : Γ(S, ⊤) ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)

def affineAlgebraScheme : Over S :=
  Over.mk (Spec.map (affineBaseAlgebraMap S B) ≫ S.isoSpec.inv)

def affineAlgebraPoint (T : Over S) (p : T ⟶ affineAlgebraScheme S B) :
    letI : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
    B →ₐ[Γ(S, ⊤)] Γ(T.left, ⊤) := by
  letI : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  refine { __ := globalRingPointEquiv T.left (CommRingCat.of B) p.left, commutes' := ?_ }
  intro r
  have he : p.left ≫ Spec.map (affineBaseAlgebraMap S B) = T.hom ≫ S.toSpecΓ := by
    have hw := congrArg (fun a => a ≫ S.toSpecΓ) p.w
    simpa only [affineAlgebraScheme, Over.mk_left, Over.mk_hom, Category.assoc,
      Scheme.isoSpec_inv_toSpecΓ, Category.comp_id] using hw
  have hr := congrArg (globalRingPointEquiv T.left Γ(S, ⊤)) he
  rw [globalRingPointEquiv_target, globalRingPointEquiv_source, globalRingPointEquiv_toSpecΓ,
    RingHom.comp_id] at hr
  exact RingHom.congr_fun hr r

def affineAlgebraPointInv (T : Over S) :
    letI : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
    (B →ₐ[Γ(S, ⊤)] Γ(T.left, ⊤)) → (T ⟶ affineAlgebraScheme S B) := by
  letI : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  intro φ
  refine Over.homMk ((globalRingPointEquiv T.left (CommRingCat.of B)).symm φ.toRingHom) ?_
  apply (cancel_mono S.toSpecΓ).mp
  change ((globalRingPointEquiv T.left (CommRingCat.of B)).symm φ.toRingHom) ≫
    (Spec.map (affineBaseAlgebraMap S B) ≫ S.isoSpec.inv) ≫ S.toSpecΓ = _
  rw [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.comp_id]
  apply (globalRingPointEquiv T.left Γ(S, ⊤)).injective
  rw [globalRingPointEquiv_target, Equiv.apply_symm_apply, globalRingPointEquiv_source,
    globalRingPointEquiv_toSpecΓ, RingHom.comp_id]
  exact φ.comp_algebraMap

def affineAlgebraPointEquiv (T : Over S) :
    letI : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
    (T ⟶ affineAlgebraScheme S B) ≃ (B →ₐ[Γ(S, ⊤)] Γ(T.left, ⊤)) := by
  letI : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  exact {
    toFun := affineAlgebraPoint S B T
    invFun := affineAlgebraPointInv S B T
    left_inv p := by
      apply Over.OverMorphism.ext
      exact (globalRingPointEquiv T.left (CommRingCat.of B)).symm_apply_apply p.left
    right_inv φ := by
      apply AlgHom.ext
      intro b
      exact RingHom.congr_fun ((globalRingPointEquiv T.left (CommRingCat.of B)).apply_symm_apply φ.toRingHom) b }

theorem affineAlgebraPointEquiv_apply (T : Over S) (p : T ⟶ affineAlgebraScheme S B) (b : B) :
    affineAlgebraPointEquiv S B T p b = p.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := rfl

theorem affineAlgebraPointEquiv_composite {T T' : Scheme.{u}} (g : T ⟶ S) (t : T' ⟶ T)
    (p : Over.mk g ⟶ affineAlgebraScheme S B) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(T', ⊤) := (t ≫ g).appTop.hom.toAlgebra
    affineAlgebraPointEquiv S B (Over.mk (t ≫ g))
      ((Over.homMk t rfl : Over.mk (t ≫ g) ⟶ Over.mk g) ≫ p) =
    (ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom rfl).comp
      (affineAlgebraPointEquiv S B (Over.mk g) p) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(T', ⊤) := (t ≫ g).appTop.hom.toAlgebra
  change (affineAlgebraPointEquiv S B (Over.mk (t ≫ g))
    ((Over.homMk t rfl : Over.mk (t ≫ g) ⟶ Over.mk g) ≫ p) : B →ₐ[Γ(S, ⊤)] Γ(T', ⊤)) = _
  apply AlgHom.ext (R := Γ(S, ⊤)) (A := B) (B := Γ(T', ⊤))
  intro b
  change t.appTop (p.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) =
    ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom rfl
      (p.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))
  exact (ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq_apply g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom rfl _).symm

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints
