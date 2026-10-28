import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! # Frobenius -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction

noncomputable section

/-!
# Completion: the q-power Frobenius on schemes over a finite field

The maps below are constructed on the structure sheaf and shown to be
local on stalks. The field cardinality may be any prime power. No
cohomological action or weight assertion is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] [Fintype k]

/-- The q-power ring map for a ring receiving the finite field. -/
def finiteFieldPowerRingHom {R : Type u} [CommRing R] (κ : k →+* R) : R →+* R :=
  letI : Algebra k R := κ.toAlgebra
  (FiniteField.frobeniusAlgHom k R).toRingHom

@[simp]
theorem finiteFieldPowerRingHom_apply {R : Type u} [CommRing R]
    (κ : k →+* R) (r : R) :
    finiteFieldPowerRingHom k κ r = r ^ Fintype.card k := rfl

variable (X : Scheme.{u}) (κ : k →+* Γ(X, ⊤))

/-- The base field acts on the sections of every open. -/
def sectionBaseMap (U : X.Opens) : k →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp κ

/-- Frobenius on the ringed space fixes the topological space. -/
def qPowerRingedFrobenius : X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c := {
    app := fun U => CommRingCat.ofHom
      (finiteFieldPowerRingHom k (sectionBaseMap k X κ U.unop))
    naturality := by
      intro U V f
      ext s
      exact (map_pow (X.presheaf.map f).hom s (Fintype.card k)).symm
  }

theorem qPowerRingedFrobenius_stalk (x : X) (a : X.presheaf.stalk x) :
    (qPowerRingedFrobenius k X κ).stalkMap x a = a ^ Fintype.card k := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  erw [PresheafedSpace.stalkMap_germ_apply]
  exact map_pow (X.presheaf.germ U x hxU).hom s (Fintype.card k)

/-- The q-power map is a genuine morphism of schemes. -/
def qPowerSchemeFrobenius : X ⟶ X where
  toHom := qPowerRingedFrobenius k X κ
  prop x := {
    map_nonunit := by
      intro a ha
      have hp : IsUnit (a ^ Fintype.card k) :=
        (qPowerRingedFrobenius_stalk k X κ x a) ▸ ha
      exact (isUnit_pow_iff Fintype.card_pos.ne').mp hp
  }

@[simp]
theorem qPowerSchemeFrobenius_apply (x : X) :
    qPowerSchemeFrobenius k X κ x = x := rfl

@[simp]
theorem qPowerSchemeFrobenius_app (U : X.Opens) (s : Γ(X, U)) :
    (qPowerSchemeFrobenius k X κ).app U s = s ^ Fintype.card k := rfl

@[simp]
theorem qPowerSchemeFrobenius_appTop (s : Γ(X, ⊤)) :
    (qPowerSchemeFrobenius k X κ).appTop s = s ^ Fintype.card k := rfl

/-- q-power Frobenius commutes with every morphism of the underlying schemes. -/
theorem qPowerSchemeFrobenius_naturality
    {Y : Scheme.{u}} (κY : k →+* Γ(Y, ⊤)) (f : X ⟶ Y) :
    qPowerSchemeFrobenius k X κ ≫ f = f ≫ qPowerSchemeFrobenius k Y κY := by
  apply Scheme.Hom.ext (by rfl)
  intro U
  change (f.app U ≫ (qPowerSchemeFrobenius k X κ).app (f ⁻¹ᵁ U)) ≫
    X.presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) =
      (qPowerSchemeFrobenius k Y κY).app U ≫ f.app U
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  exact (map_pow (f.app U).hom s (Fintype.card k)).symm

variable (A : Over (Spec (CommRingCat.of k)))

/-- The base-field map induced by the structure morphism. -/
def varietyBaseMap : k →+* Γ(A.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ A.hom.appTop).hom

theorem qPowerSchemeFrobenius_over :
    qPowerSchemeFrobenius k A.left (varietyBaseMap k A) ≫ A.hom = A.hom := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (A.hom.appTop ≫ (qPowerSchemeFrobenius k A.left (varietyBaseMap k A)).appTop) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ A.hom.appTop
  ext x
  change (qPowerSchemeFrobenius k A.left (varietyBaseMap k A)).appTop
      (varietyBaseMap k A x) = varietyBaseMap k A x
  rw [qPowerSchemeFrobenius_appTop, ← map_pow, FiniteField.pow_card]

/-- The q-power Frobenius endomorphism over the finite ground field. -/
def finiteFieldSchemeFrobenius : A ⟶ A :=
  Over.homMk (qPowerSchemeFrobenius k A.left (varietyBaseMap k A))
    (qPowerSchemeFrobenius_over k A)

theorem finiteFieldSchemeFrobenius_naturality
    {B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    finiteFieldSchemeFrobenius k A ≫ f = f ≫ finiteFieldSchemeFrobenius k B := by
  apply Over.OverMorphism.ext
  exact qPowerSchemeFrobenius_naturality k A.left (varietyBaseMap k A)
    (varietyBaseMap k B) f.left

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem finiteFieldSchemeFrobenius_unit :
    finiteFieldSchemeFrobenius k (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _ :=
  Subsingleton.elim _ _

theorem finiteFieldSchemeFrobenius_tensor
    (B : Over (Spec (CommRingCat.of k))) :
    finiteFieldSchemeFrobenius k (A ⊗ B) =
      finiteFieldSchemeFrobenius k A ⊗ₘ finiteFieldSchemeFrobenius k B := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [tensorHom_fst]
    exact finiteFieldSchemeFrobenius_naturality k (A ⊗ B) (fst A B)
  · rw [tensorHom_snd]
    exact finiteFieldSchemeFrobenius_naturality k (A ⊗ B) (snd A B)

/-- In particular, Frobenius is an algebraic group endomorphism. -/
instance finiteFieldSchemeFrobenius_isMonHom [MonObj A] :
    IsMonHom (finiteFieldSchemeFrobenius k A) where
  one_hom := by
    have h := finiteFieldSchemeFrobenius_naturality k (𝟙_ _) η[A]
    simpa only [finiteFieldSchemeFrobenius_unit, Category.id_comp] using h.symm
  mul_hom := by
    have h := finiteFieldSchemeFrobenius_naturality k (A ⊗ A) μ[A]
    rw [finiteFieldSchemeFrobenius_tensor] at h
    exact h.symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction
