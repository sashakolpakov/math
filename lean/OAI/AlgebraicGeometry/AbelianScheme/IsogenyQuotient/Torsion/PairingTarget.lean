import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Pairing Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
A pairing on n-torsion factors through the actual n-torsion kernel of its
target. This constructs the root-of-unity-valued map when the original
target is G_m, and preserves the relative annihilator on all test schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem Torsion.PairingTarget.Construction.nativeTorsionScheme_identity_killed {S : Scheme.{u}}
    (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    (𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A n)) ^ n = 1 := by
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A n)).mp
  rw [MonObj.pow_comp, Category.id_comp, Torsion.Groups.Construction.nativeTorsionInclusion_killed, MonObj.one_comp]

variable {S : Scheme.{u}} {A B W P : Over S} [GrpObj A] [GrpObj B]
  [GrpObj W] [IsCommMonObj W]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
  (n : ℕ) (hA : (𝟙 A) ^ n = 1)

include hA in
theorem Annihilator.Construction.SchemeBicharacter.pairValue_pow_eq_one (X : Over S) (x : X ⟶ A) (y : X ⟶ B) :
    (e.pairValue x y) ^ n = 1 := by
  have hx : x ^ n = 1 := by
    have h := congrArg (fun f : A ⟶ A => x ≫ f) hA
    simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using h
  change (e.pairLeftHom y x) ^ n = 1
  rw [← map_pow, hx, map_one]

include hA in
theorem Annihilator.Construction.SchemeBicharacter.hom_pow_eq_one : e.hom ^ n = 1 := by
  have h := e.pairValue_pow_eq_one n hA (A ⊗ B) (fst A B) (snd A B)
  simpa only [Annihilator.Construction.SchemeBicharacter.pairValue, lift_fst_snd, Category.id_comp] using h

def Annihilator.Construction.SchemeBicharacter.torsionTargetHom : A ⊗ B ⟶ Torsion.Groups.Construction.nativeTorsionScheme W n :=
  Torsion.Groups.Construction.nativeTorsionLift W n e.hom (e.hom_pow_eq_one n hA)

theorem Annihilator.Construction.SchemeBicharacter.torsionTargetHom_inclusion :
    e.torsionTargetHom n hA ≫ Torsion.Groups.Construction.nativeTorsionInclusion W n = e.hom :=
  Torsion.Groups.Construction.nativeTorsionLift_inclusion W n e.hom (e.hom_pow_eq_one n hA)

def Annihilator.Construction.SchemeBicharacter.torsionTarget : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := Torsion.Groups.Construction.nativeTorsionScheme W n) where
  hom := e.torsionTargetHom n hA
  one_left X y := by
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion W n)).mp
    rw [Category.assoc, Annihilator.Construction.SchemeBicharacter.torsionTargetHom_inclusion, MonObj.one_comp]
    exact e.one_left X y
  one_right X x := by
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion W n)).mp
    rw [Category.assoc, Annihilator.Construction.SchemeBicharacter.torsionTargetHom_inclusion, MonObj.one_comp]
    exact e.one_right X x
  mul_left X x z y := by
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion W n)).mp
    simp only [MonObj.mul_comp, Category.assoc, Annihilator.Construction.SchemeBicharacter.torsionTargetHom_inclusion]
    exact e.mul_left X x z y
  mul_right X x y z := by
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion W n)).mp
    simp only [MonObj.mul_comp, Category.assoc, Annihilator.Construction.SchemeBicharacter.torsionTargetHom_inclusion]
    exact e.mul_right X x y z

theorem Annihilator.Construction.SchemeBicharacter.torsionTarget_pairValue_inclusion {X : Over S} (x : X ⟶ A) (y : X ⟶ B) :
    (e.torsionTarget n hA).pairValue x y ≫ Torsion.Groups.Construction.nativeTorsionInclusion W n = e.pairValue x y := by
  change (lift x y ≫ e.torsionTargetHom n hA) ≫ Torsion.Groups.Construction.nativeTorsionInclusion W n = _
  rw [Category.assoc, Annihilator.Construction.SchemeBicharacter.torsionTargetHom_inclusion]
  rfl

theorem Annihilator.Construction.SchemeBicharacter.torsionTarget_pairValue_eq_one {X : Over S} (x : X ⟶ A) (y : X ⟶ B) :
    (e.torsionTarget n hA).pairValue x y = 1 ↔ e.pairValue x y = 1 := by
  rw [← cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion W n), Annihilator.Construction.SchemeBicharacter.torsionTarget_pairValue_inclusion,
    MonObj.one_comp]

theorem Annihilator.Construction.SchemeBicharacter.torsionTarget_relativeAnnihilator (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    (e.torsionTarget n hA).relativeAnnihilator F = e.relativeAnnihilator F := by
  ext X t y
  change (∀ (Y : Over S) (f : Y ⟶ X) (x : Y ⟶ A), x ∈ F.points Y (f ≫ t) →
    (e.torsionTarget n hA).pairValue x (f ≫ y) = 1) ↔ _
  simp only [Annihilator.Construction.SchemeBicharacter.torsionTarget_pairValue_eq_one]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
