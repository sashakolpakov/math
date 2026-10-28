import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Open Over -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.OpenOver.Construction

noncomputable section

/-! Open subschemes and factorization maps in a category of schemes over a base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def overOpen {S : Scheme.{u}} (X : Over S) (V : X.left.Opens) : Over S :=
  Over.mk (V.ι ≫ X.hom)

def overOpenInclusion {S : Scheme.{u}} (X : Over S) (V : X.left.Opens) :
    overOpen X V ⟶ X := Over.homMk V.ι rfl

instance {S : Scheme.{u}} (X : Over S) (V : X.left.Opens) :
    IsOpenImmersion (overOpenInclusion X V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)

instance {S : Scheme.{u}} (X : Over S) (V : X.left.Opens) :
    Mono (overOpenInclusion X V) := Over.mono_of_mono_left _

instance {S : Scheme.{u}} (X : Over S) [IsReduced X.left] (V : X.left.Opens) :
    IsReduced (overOpen X V).left := inferInstanceAs (IsReduced V.toScheme)

theorem range_subset_of_overOpen_factor {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (V : Y.left.Opens) (k : X ⟶ overOpen Y V)
    (h : k ≫ overOpenInclusion Y V = f) : Set.range f.left ⊆ (V : Set Y.left) := by
  rw [← h]
  rintro _ ⟨x, rfl⟩
  exact (k.left x).property

def overOpenLift {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (V : Y.left.Opens)
    (h : Set.range f.left ⊆ (V : Set Y.left)) : X ⟶ overOpen Y V := by
  let l : X.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι f.left (by simpa using h)
  have hl : l ≫ V.ι = f.left := IsOpenImmersion.lift_fac _ _ _
  exact Over.homMk l ((Category.assoc l V.ι Y.hom).symm.trans
    ((congrArg (fun a ↦ a ≫ Y.hom) hl).trans f.w))

@[reassoc (attr := simp)]
theorem overOpenLift_inclusion {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (V : Y.left.Opens) (h : Set.range f.left ⊆ (V : Set Y.left)) :
    overOpenLift f V h ≫ overOpenInclusion Y V = f := by
  apply Over.OverMorphism.ext
  have H := IsOpenImmersion.lift_fac V.ι f.left (by simpa using h)
  exact H

@[reassoc]
theorem overOpenLift_left_ι {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (V : Y.left.Opens) (h : Set.range f.left ⊆ (V : Set Y.left)) :
    (overOpenLift f V h).left ≫ V.ι = f.left := by
  have H := IsOpenImmersion.lift_fac V.ι f.left (by simpa using h)
  exact H

theorem overOpenLift_dominant {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsDominant f.left]
    (V : Y.left.Opens) (h : Set.range f.left ⊆ (V : Set Y.left)) :
    IsDominant (overOpenLift f V h).left := by
  have : IsDominant ((overOpenLift f V h).left ≫ (overOpenInclusion Y V).left) := by
    change IsDominant ((overOpenLift f V h).left ≫ V.ι)
    rw [overOpenLift_left_ι]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion (overOpenLift f V h).left
    (overOpenInclusion Y V).left

def overOpenRestrict {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (V : Y.left.Opens) :
    overOpen X (f.left ⁻¹ᵁ V) ⟶ overOpen Y V :=
  Over.homMk (f.left ∣_ V) (by
    change (f.left ∣_ V) ≫ (V.ι ≫ Y.hom) = (f.left ⁻¹ᵁ V).ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, f.w])

@[reassoc (attr := simp)]
theorem overOpenRestrict_inclusion {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (V : Y.left.Opens) :
    overOpenRestrict f V ≫ overOpenInclusion Y V =
      overOpenInclusion X (f.left ⁻¹ᵁ V) ≫ f := by
  apply Over.OverMorphism.ext
  exact morphismRestrict_ι f.left V

theorem overOpenInclusion_range {S : Scheme.{u}} (X : Over S) (V : X.left.Opens) :
    Set.range (overOpenInclusion X V).left = (V : Set X.left) := V.range_ι

theorem over_hom_ext_of_dominant
    {S : Scheme.{u}} {W X Y : Over S} [IsReduced X.left] [IsSeparated Y.hom]
    (d : W ⟶ X) [IsDominant d.left] (f g : X ⟶ Y) (h : d ≫ f = d ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.hom (f.w.trans g.w.symm) d.left
    (congrArg (fun k ↦ k.left) h)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.OpenOver.Construction
