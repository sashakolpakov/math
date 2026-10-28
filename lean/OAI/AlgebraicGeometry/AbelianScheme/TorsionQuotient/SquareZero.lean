import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.InfinitesimalRootsIn
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Square Zero -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts

/-!
# TorsionQuotient: the module of square-zero lifts of a ring map

These constructions do not require a Hopf algebra. They apply in particular
to local maps out of scheme stalks, so that infinitesimal linearization can
be used for schemes which are not affine.
-/

variable {A A' C : Type*} [CommRing A] [CommRing A'] [CommRing C]

/-- Congruence modulo a square-zero ideal preserves localness. -/
theorem isLocalHom_of_congruent
    (J : Ideal C) (hJ : J ^ 2 = ⊥) (e f : A →+* C) [IsLocalHom e]
    (hf : ∀ a, f a - e a ∈ J) : IsLocalHom f where
  map_nonunit a ha := by
    have hmem : e a - f a ∈ J := by
      simpa only [neg_sub] using J.neg_mem (hf a)
    have hn : IsNilpotent (e a - f a) :=
      ⟨2, by simpa only [pow_two] using
        InfinitesimalEq.Infinitesimal.mul_eq_zero_of_square_zero_ideal J hJ hmem hmem⟩
    have he : IsUnit (e a) := by
      simpa only [sub_add_cancel] using hn.isUnit_add_right_of_commute ha (Commute.all ..)
    exact isUnit_of_map_unit e a he

/-- Affine interpolation, as an actual ring homomorphism. -/
def interpolate (J : Ideal C) (hJ : J ^ 2 = ⊥) (e f : A →+* C)
    (hf : ∀ a, f a - e a ∈ J) (c : C) : A →+* C :=
  (InfinitesimalRootsIn.InfinitesimalRoots.interpolateAlgHom J hJ e.toIntAlgHom f.toIntAlgHom hf c).toRingHom

/-- Addition of two infinitesimal deviations from the same base map. -/
def addMaps (J : Ideal C) (hJ : J ^ 2 = ⊥) (e f g : A →+* C)
    (hf : ∀ a, f a - e a ∈ J) (hg : ∀ a, g a - e a ∈ J) : A →+* C where
  toFun a := f a + g a - e a
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [map_add]; ring
  map_mul' a b := by
    have h₁ := InfinitesimalEq.Infinitesimal.mul_eq_zero_of_square_zero_ideal J hJ (hf a) (hg b)
    have h₂ := InfinitesimalEq.Infinitesimal.mul_eq_zero_of_square_zero_ideal J hJ (hg a) (hf b)
    simp only [map_mul]
    linear_combination -h₁ - h₂

/-- All ring maps reducing to e modulo J. -/
@[ext]
structure Lift (J : Ideal C) (_hJ : J ^ 2 = ⊥) (e : A →+* C) where
  hom : A →+* C
  congruent : ∀ a, hom a - e a ∈ J

namespace Lift

variable {J : Ideal C} {hJ : J ^ 2 = ⊥} {e : A →+* C}

instance : Zero (Lift J hJ e) := ⟨⟨e, fun _ => by simp⟩⟩

instance : Add (Lift J hJ e) where
  add f g := ⟨addMaps J hJ e f.hom g.hom f.congruent g.congruent, fun a => by
    change f.hom a + g.hom a - e a - e a ∈ J
    convert J.add_mem (f.congruent a) (g.congruent a) using 1
    ring⟩

instance : SMul C (Lift J hJ e) where
  smul c f := ⟨interpolate J hJ e f.hom f.congruent c, fun a => by
    change e a + c * (f.hom a - e a) - e a ∈ J
    rw [add_sub_cancel_left]
    exact J.mul_mem_left c (f.congruent a)⟩

instance : Neg (Lift J hJ e) := ⟨fun f => (-1 : C) • f⟩

@[simp] theorem zero_hom (a : A) : (0 : Lift J hJ e).hom a = e a := rfl
@[simp] theorem add_hom (f g : Lift J hJ e) (a : A) :
    (f + g).hom a = f.hom a + g.hom a - e a := rfl
@[simp] theorem smul_hom (c : C) (f : Lift J hJ e) (a : A) :
    (c • f).hom a = e a + c * (f.hom a - e a) := rfl
@[simp] theorem neg_hom (f : Lift J hJ e) (a : A) :
    (-f).hom a = e a + (-1 : C) * (f.hom a - e a) := rfl

instance : AddCommGroup (Lift J hJ e) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc f g h := by apply Lift.ext; ext a; simp only [add_hom]; ring
  zero_add f := by apply Lift.ext; ext a; simp only [add_hom, zero_hom]; ring
  add_zero f := by apply Lift.ext; ext a; simp only [add_hom, zero_hom]; ring
  neg_add_cancel f := by apply Lift.ext; ext a; simp only [add_hom, neg_hom, zero_hom]; ring
  add_comm f g := by apply Lift.ext; ext a; simp only [add_hom]; ring

instance : Module C (Lift J hJ e) where
  smul := (· • ·)
  one_smul f := by apply Lift.ext; ext a; simp only [smul_hom]; ring
  mul_smul c d f := by apply Lift.ext; ext a; simp only [smul_hom]; ring
  smul_zero c := by apply Lift.ext; ext a; simp only [smul_hom, zero_hom]; ring
  smul_add c f g := by apply Lift.ext; ext a; simp only [smul_hom, add_hom]; ring
  zero_smul f := by apply Lift.ext; ext a; simp only [smul_hom, zero_hom]; ring
  add_smul c d f := by apply Lift.ext; ext a; simp only [smul_hom, add_hom]; ring

instance (f : Lift J hJ e) [IsLocalHom e] : IsLocalHom f.hom :=
  isLocalHom_of_congruent J hJ e f.hom f.congruent

/-- Pulling back functions along a ring homomorphism is linear on lifts. -/
def comap (p : A' →+* A) : Lift J hJ e →ₗ[C] Lift J hJ (e.comp p) where
  toFun f := ⟨f.hom.comp p, fun a => f.congruent (p a)⟩
  map_add' f g := by apply Lift.ext; ext a; rfl
  map_smul' c f := by apply Lift.ext; ext a; rfl

/-- Coordinates of the infinitesimal deviation, without choosing generators. -/
def deviation : Lift J hJ e →ₗ[C] (A → C) where
  toFun f a := f.hom a - e a
  map_add' f g := by ext a; simp only [add_hom, Pi.add_apply]; ring
  map_smul' c f := by
    ext a
    simp only [smul_hom, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem deviation_injective : Function.Injective (deviation (J := J) (hJ := hJ) (e := e)) := by
  intro f g h
  apply Lift.ext
  ext a
  calc
    f.hom a = (f.hom a - e a) + e a := (sub_add_cancel _ _).symm
    _ = (g.hom a - e a) + e a := congrArg (fun z => z + e a) (congrFun h a)
    _ = g.hom a := sub_add_cancel _ _

end Lift

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts
