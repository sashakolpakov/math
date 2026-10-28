import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite

/-! # Ordinary Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction

noncomputable section

/-!
Geometric q-rank is unchanged by a finite-kernel surjection of divisible
abelian point groups. The two exact sequences through the inverse image of
the kernel give the same torsion cardinality. This is the group calculation
needed to keep the kernel operators on the ordinary locus.
-/

variable {A B : Type*} [CommGroup A] [CommGroup B]

abbrev qTorsion (A : Type*) [CommGroup A] (q : ℕ) :=
  (powMonoidHom q : A →* A).ker

abbrev kernelPowerPreimage (f : A →* B) (q : ℕ) :=
  f.ker.comap (powMonoidHom q : A →* A)

def powerToKernel (f : A →* B) (q : ℕ) : kernelPowerPreimage f q →* f.ker where
  toFun x := ⟨x.val ^ q, x.property⟩
  map_one' := Subtype.ext (one_pow q)
  map_mul' x y := Subtype.ext (mul_pow x.val y.val q)

def imageToTorsion (f : A →* B) (q : ℕ) : kernelPowerPreimage f q →* qTorsion B q where
  toFun x := ⟨f x.val, by
    change (f x.val) ^ q = 1
    rw [← f.map_pow]
    exact x.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x.val y.val)

def powerToKernelKernelEquiv (f : A →* B) (q : ℕ) :
    (powerToKernel f q).ker ≃ qTorsion A q where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change f (x.val ^ q) = 1
    have hx : x.val ^ q = 1 := x.property
    rw [hx, f.map_one]⟩, Subtype.ext x.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

def imageToTorsionKernelEquiv (f : A →* B) (q : ℕ) :
    (imageToTorsion f q).ker ≃ f.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change f (x.val ^ q) = 1
    have hx : f x.val = 1 := x.property
    rw [f.map_pow, hx, one_pow]⟩, Subtype.ext x.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem card_kernel_mul_of_surjective
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card H = Nat.card G := by
  have hi : f.ker.index = Nat.card H :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [← hi]
  exact f.ker.card_mul_index

/-- Only kernel points need q-division lifts. For a q-power kernel these
come from the ordinary q-divisible torsion tower. -/
theorem qTorsion_card_eq_of_kernel_divisible
    (f : A →* B) [Finite f.ker] (hf : Function.Surjective f)
    (q : ℕ) (hdiv : ∀ k : f.ker, ∃ a : A, a ^ q = k.val) :
    Nat.card (qTorsion A q) = Nat.card (qTorsion B q) := by
  have hpower : Function.Surjective (powerToKernel f q) := by
    intro k
    obtain ⟨a, ha⟩ := hdiv k
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    change f (a ^ q) = 1
    rw [ha]
    exact k.property
  have himage : Function.Surjective (imageToTorsion f q) := by
    intro b
    obtain ⟨a, ha⟩ := hf b.val
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    change f (a ^ q) = 1
    rw [f.map_pow, ha]
    exact b.property
  have h₁ := card_kernel_mul_of_surjective (powerToKernel f q) hpower
  have h₂ := card_kernel_mul_of_surjective (imageToTorsion f q) himage
  rw [Nat.card_congr (powerToKernelKernelEquiv f q)] at h₁
  rw [Nat.card_congr (imageToTorsionKernelEquiv f q)] at h₂
  have h := h₂.trans h₁.symm
  rw [Nat.mul_comm (Nat.card (qTorsion A q))] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.ker)) h).symm

/-- A finite-kernel isogeny preserves geometric q-torsion cardinality
when the source point group is q-divisible. -/
theorem qTorsion_card_eq_of_finite_kernel
    (f : A →* B) [Finite f.ker] (hf : Function.Surjective f)
    (q : ℕ) (hdiv : Function.Surjective (fun a : A => a ^ q)) :
    Nat.card (qTorsion A q) = Nat.card (qTorsion B q) :=
  qTorsion_card_eq_of_kernel_divisible f hf q (fun k => hdiv k.val)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction
