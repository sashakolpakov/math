import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator

/-! # Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy.Construction

noncomputable section

/-!
Relative maximal isotropy for a split pair, on all test schemes. The only
duality input is CartierDuality's explicit double-annihilator identity for the actual
relative annihilator. The computation does not replace families by their
geometric points and does not assume a polarized quotient exists.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B W P : Over S} [GrpObj A] [GrpObj B] [GrpObj W]

namespace SchemeBicharacter

variable (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))

def _root_.OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.pairLeftHom {X : Over S} (y : X ⟶ B) : (X ⟶ A) →* (X ⟶ W) where
  toFun x := e.pairValue x y
  map_one' := e.one_left X y
  map_mul' x z := e.mul_left X x z y

omit [GrpObj A] [GrpObj B] in
private theorem lift_swap {X : Over S} (x : X ⟶ A) (y : X ⟶ B) :
    lift y x ≫ (β_ B A).hom = lift x y := by
  apply hom_ext <;> simp

def _root_.OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.flip : Annihilator.Construction.SchemeBicharacter (A := B) (B := A) (W := W) where
  hom := (β_ B A).hom ≫ e.hom
  one_left X x := by
    rw [← Category.assoc, lift_swap]
    exact e.one_right X x
  one_right X y := by
    rw [← Category.assoc, lift_swap]
    exact e.one_left X y
  mul_left X y z x := by
    simp only [← Category.assoc, lift_swap]
    exact e.mul_right X x y z
  mul_right X y x z := by
    simp only [← Category.assoc, lift_swap]
    exact e.mul_left X x z y

@[simp]
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.flip_pairValue {X : Over S} (y : X ⟶ B) (x : X ⟶ A) :
    e.flip.pairValue y x = e.pairValue x y := by
  change lift y x ≫ ((β_ B A).hom ≫ e.hom) = lift x y ≫ e.hom
  rw [← Category.assoc, lift_swap]

end SchemeBicharacter

/-- The product of two subgroup families inside the split product group. -/
def pairedRelativeSubgroup (H : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (J : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup (A ⊗ B) P where
  points X t :=
    ((H.points X t).comap (IsMonHom.monoidHom (fst A B) X)) ⊓
      ((J.points X t).comap (IsMonHom.monoidHom (snd A B) X))
  naturality := by
    intro X Y f t z hz
    exact ⟨by
      change (f ≫ z) ≫ fst A B ∈ H.points X (f ≫ t)
      rw [Category.assoc]
      exact H.naturality f t hz.1,
      by
        change (f ≫ z) ≫ snd A B ∈ J.points X (f ≫ t)
        rw [Category.assoc]
        exact J.naturality f t hz.2⟩

variable (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))

/-- Orthogonality for e(x,y')/e(x',y), expressed as equality of the two
values. The quantification includes every change of test scheme. -/
def relativeSplitOrthogonal (L : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (A ⊗ B) P) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup (A ⊗ B) P where
  points X t := {
    carrier := {z | ∀ (Y : Over S) (f : Y ⟶ X) (w : Y ⟶ A ⊗ B),
      w ∈ L.points Y (f ≫ t) →
      e.pairValue (w ≫ fst A B) (f ≫ z ≫ snd A B) =
        e.pairValue (f ≫ z ≫ fst A B) (w ≫ snd A B)}
    one_mem' := by
      intro Y f w _
      simp only [MonObj.one_comp, MonObj.comp_one]
      exact (e.one_right Y _).trans (e.one_left Y _).symm
    mul_mem' := by
      intro x y hx hy Y f w hw
      simp only [MonObj.mul_comp, MonObj.comp_mul]
      change e.pairRightHom (w ≫ fst A B) (_ * _) = e.pairLeftHom (w ≫ snd A B) (_ * _)
      rw [map_mul, map_mul]
      change e.pairValue _ _ * e.pairValue _ _ = e.pairValue _ _ * e.pairValue _ _
      rw [hx Y f w hw, hy Y f w hw]
    inv_mem' := by
      intro z hz Y f w hw
      simp only [GrpObj.inv_comp, GrpObj.comp_inv]
      change e.pairRightHom (w ≫ fst A B) _⁻¹ = e.pairLeftHom (w ≫ snd A B) _⁻¹
      rw [map_inv, map_inv]
      change (e.pairValue _ _)⁻¹ = (e.pairValue _ _)⁻¹
      rw [hz Y f w hw] }
  naturality := by
    intro X Y f t z hz Z g w hw
    simpa only [Category.assoc] using
      hz Z (g ≫ f) w (by simpa only [Category.assoc] using hw)

/-- Compute the orthogonal subgroup of a split product in families. -/
theorem relativeSplitOrthogonal_product
    (H : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (J : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) :
    relativeSplitOrthogonal e (pairedRelativeSubgroup H J) =
      pairedRelativeSubgroup (e.flip.relativeAnnihilator J) (e.relativeAnnihilator H) := by
  ext X t z
  constructor
  · intro hz
    constructor
    · intro Y f y hy
      change e.flip.pairValue y (f ≫ z ≫ fst A B) = 1
      have hw : lift (1 : Y ⟶ A) y ∈ (pairedRelativeSubgroup H J).points Y (f ≫ t) := by
        change (lift 1 y ≫ fst A B ∈ H.points Y (f ≫ t)) ∧
          (lift 1 y ≫ snd A B ∈ J.points Y (f ≫ t))
        simpa only [lift_fst, lift_snd] using And.intro (H.points Y (f ≫ t)).one_mem hy
      have h := hz Y f (lift 1 y) hw
      simp only [lift_fst, lift_snd] at h
      rw [show e.pairValue (1 : Y ⟶ A) (f ≫ z ≫ snd A B) = 1 from e.one_left Y _] at h
      rw [Annihilator.Construction.SchemeBicharacter.flip_pairValue]
      exact h.symm
    · intro Y f x hx
      change e.pairValue x (f ≫ z ≫ snd A B) = 1
      have hw : lift x (1 : Y ⟶ B) ∈ (pairedRelativeSubgroup H J).points Y (f ≫ t) := by
        change (lift x 1 ≫ fst A B ∈ H.points Y (f ≫ t)) ∧
          (lift x 1 ≫ snd A B ∈ J.points Y (f ≫ t))
        simpa only [lift_fst, lift_snd] using And.intro hx (J.points Y (f ≫ t)).one_mem
      have h := hz Y f (lift x 1) hw
      simp only [lift_fst, lift_snd] at h
      rw [show e.pairValue (f ≫ z ≫ fst A B) (1 : Y ⟶ B) = 1 from e.one_right Y _] at h
      exact h
  · rintro ⟨hx, hy⟩ Y f w hw
    have hleft := hy Y f (w ≫ fst A B) hw.1
    have hright := hx Y f (w ≫ snd A B) hw.2
    simp only [Annihilator.Construction.SchemeBicharacter.flip_pairValue] at hleft hright
    exact hleft.trans hright.symm

/-- CartierDuality's relative double-annihilator conclusion makes the constructed
chosen/opposite pair self-annihilating on every test scheme. -/
theorem relative_maximal_isotropic_of_CartierDuality
    (H : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (h_CartierDuality : e.flip.relativeAnnihilator (e.relativeAnnihilator H) = H) :
    relativeSplitOrthogonal e (pairedRelativeSubgroup H (e.relativeAnnihilator H)) =
      pairedRelativeSubgroup H (e.relativeAnnihilator H) := by
  rw [relativeSplitOrthogonal_product, h_CartierDuality]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy.Construction
