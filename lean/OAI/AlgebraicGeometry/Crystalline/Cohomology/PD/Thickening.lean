import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.DividedPowers.DPMorphism

/-! # Thickening -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening

noncomputable section

/-!
# Cohomology: affine divided-power thickenings

This defines the algebraic objects underlying affine crystalline thickenings
of a fixed affine special fibre over the Witt-vector divided-power base.
Arrows here are ring maps; passing to affine schemes reverses their direction.
The affine crystalline site and its topology are constructed separately.
Nilpotence of `p` is imposed on the ambient ring; the divided-power ideal
is then locally nilpotent, without a uniform ideal-nilpotence requirement.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]
variable (A : Type u) [CommRing A] [Algebra k A]

/-- An affine crystalline thickening with divided powers compatible with those
on the Witt-vector base. These are geometric defining conditions, not
cohomological assumptions. -/
structure AffinePDThickening where
  ring : CommRingCat.{u}
  [baseAlgebra : Algebra (WittVector p k) ring]
  reduction : ring →+* A
  reduction_surjective : Function.Surjective reduction
  reduction_base : reduction.comp (algebraMap (WittVector p k) ring) =
    (algebraMap k A).comp WittVector.constantCoeff
  p_nilpotent : IsNilpotent (p : ring)
  dividedPowers : DividedPowers (RingHom.ker reduction)
  baseDP : DividedPowers.IsDPMorphism
    (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) dividedPowers
    (algebraMap (WittVector p k) ring)

attribute [instance] AffinePDThickening.baseAlgebra

namespace AffinePDThickening

variable {p k A}

/-- Morphisms commute with reduction and preserve divided powers. -/
structure Hom (S T : AffinePDThickening p k A) where
  hom : S.ring →ₐ[WittVector p k] T.ring
  reduction_comp : T.reduction.comp hom.toRingHom = S.reduction
  dp_comp : DividedPowers.IsDPMorphism S.dividedPowers T.dividedPowers hom.toRingHom

@[ext]
theorem Hom.ext {S T : AffinePDThickening p k A} (f g : AffinePDThickening.Hom S T)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (AffinePDThickening p k A) where
  Hom := AffinePDThickening.Hom
  id S :=
    { hom := AlgHom.id (WittVector p k) S.ring
      reduction_comp := by ext; rfl
      dp_comp := (DividedPowers.DPMorphism.id S.dividedPowers).isDPMorphism }
  comp f g :=
    { hom := g.hom.comp f.hom
      reduction_comp := by
        ext x
        exact (DFunLike.congr_fun g.reduction_comp (f.hom x)).trans
          (DFunLike.congr_fun f.reduction_comp x)
      dp_comp := g.dp_comp.comp _ f.dp_comp }
  id_comp f := by apply AffinePDThickening.Hom.ext; ext; rfl
  comp_id f := by apply AffinePDThickening.Hom.ext; ext; rfl
  assoc f g h := by apply AffinePDThickening.Hom.ext; ext; rfl

/-- Forget the divided-power thickening but retain its actual ring. -/
def underlyingRing : AffinePDThickening p k A ⥤ CommRingCat where
  obj S := S.ring
  map f := CommRingCat.ofHom f.hom.toRingHom

variable (S : AffinePDThickening p k A)

/-- The residue characteristic belongs to the defining divided-power ideal. -/
theorem p_mem_kernel : (p : S.ring) ∈ RingHom.ker S.reduction := by
  have h := S.baseDP.ideal_comp (Ideal.mem_map_of_mem
    (algebraMap (WittVector p k) S.ring)
    (Ideal.subset_span (Set.mem_singleton (p : WittVector p k))))
  simpa only [map_natCast] using h

/-- The ambient ring is annihilated by a power of the residue characteristic. -/
theorem p_isNilpotent : IsNilpotent (p : S.ring) := S.p_nilpotent

/-- Each element of the defining ideal is nilpotent. No single bound for
powers of the entire ideal is required. -/
theorem kernel_element_isNilpotent (x : S.ring) (hx : x ∈ RingHom.ker S.reduction) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := S.p_nilpotent
  refine ⟨p ^ n, S.dividedPowers.nilpotent_of_mem_dpIdeal
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero) ?_ hx⟩
  intro y _hy
  rw [nsmul_eq_mul, Nat.cast_pow, hn, zero_mul]

/-- Every thickening map takes its source defining ideal into the target ideal. -/
theorem map_kernel {T : AffinePDThickening p k A} (f : S ⟶ T)
    (x : S.ring) (hx : x ∈ RingHom.ker S.reduction) :
    f.hom x ∈ RingHom.ker T.reduction := by
  change T.reduction (f.hom x) = 0
  rw [show T.reduction (f.hom x) = S.reduction x from
    DFunLike.congr_fun f.reduction_comp x]
  exact hx

end AffinePDThickening

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening
