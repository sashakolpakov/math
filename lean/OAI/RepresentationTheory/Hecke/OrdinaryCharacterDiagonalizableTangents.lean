import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Ordinary Character Diagonalizable Tangents -/

namespace OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents

noncomputable section

/-! Nonzero tangent points of split multiplicative blocks are actual
maps from the dual numbers into the group Hopf algebra's spectrum.
Their addition and scalar operations are checked on those maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k M : Type} [Field k] [CommGroup M]

abbrev groupScheme : Over (Spec (.of k)) :=
  (Spec (.of (MonoidAlgebra k M))).asOver (Spec (.of k))

def character (χ : Additive M →+ k) : M →* DualNumber k where
  toFun m := ⟨1, χ (Additive.ofMul m)⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change 1 = 1 * 1
      simp
    · change χ (Additive.ofMul a + Additive.ofMul b) =
        1 * χ (Additive.ofMul b) + χ (Additive.ofMul a) * 1
      simp [map_add, add_comm]

def pointEquiv : (M →* DualNumber k) ≃*
    (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ groupScheme (k := k) (M := M)) :=
  (MonoidAlgebra.liftMulEquiv (R := k) (M := M) (A := DualNumber k)).trans Spec.mapMulEquiv

def point (χ : Additive M →+ k) : OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ groupScheme (M := M) :=
  pointEquiv (character χ)

theorem point_left (χ : Additive M →+ k) :
    (point χ).left = Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.lift k (DualNumber k) M (character χ)).toRingHom) := rfl

theorem character_zero : character (0 : Additive M →+ k) = 1 := by
  ext m <;> rfl

theorem character_add (χ ψ : Additive M →+ k) :
    character (χ + ψ) = character χ * character ψ := by
  apply MonoidHom.ext
  intro m
  apply TrivSqZeroExt.ext
  · change 1 = 1 * 1
    simp
  · change χ (Additive.ofMul m) + ψ (Additive.ofMul m) =
      1 * ψ (Additive.ofMul m) + χ (Additive.ofMul m) * 1
    simp [add_comm]

theorem point_zero : point (0 : Additive M →+ k) = 1 := by
  rw [point, character_zero, map_one]

theorem point_add (χ ψ : Additive M →+ k) : point (χ + ψ) = point χ * point ψ := by
  rw [point, character_add, map_mul]
  rfl

def pointHom : (Additive M →+ k) →+
    Additive (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ groupScheme (M := M)) where
  toFun χ := Additive.ofMul (point χ)
  map_zero' := congrArg Additive.ofMul point_zero
  map_add' χ ψ := congrArg Additive.ofMul (point_add χ ψ)

theorem point_injective : Function.Injective (point (k := k) (M := M)) := by
  intro χ ψ h
  have hc := pointEquiv.injective h
  apply AddMonoidHom.ext
  intro m
  exact congrArg (fun f : M →* DualNumber k => (f m.toMul).snd) hc

theorem point_ne_one {χ : Additive M →+ k} (hχ : χ ≠ 0) : point χ ≠ 1 := by
  intro h
  exact hχ (point_injective (h.trans point_zero.symm))

theorem point_reduction (χ : Additive M →+ k) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ point χ = 1 := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) ≫
    Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.lift k (DualNumber k) M (character χ)).toRingHom) = _
  rw [← Spec.map_comp]
  have h : (TrivSqZeroExt.fstHom k k k).comp
      (MonoidAlgebra.lift k (DualNumber k) M (character χ)) =
        Bialgebra.counitAlgHom k (MonoidAlgebra k M) := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp [character]
      rfl
    · exact Subsingleton.elim _ _
  have h' := congrArg (fun f : MonoidAlgebra k M →ₐ[k] k =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) h
  exact h'.trans (by
    rw [Hom.one_def, Over.comp_left, one_spec_asOver_spec_left]
    exact (Category.id_comp _).symm)

theorem point_scalar (χ : Additive M →+ k) (c : k) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k c ≫ point χ = point (c • χ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.lift k (DualNumber k) M (character χ)).toRingHom) = _
  rw [← Spec.map_comp]
  have h : (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).comp
      (MonoidAlgebra.lift k (DualNumber k) M (character χ)) =
        MonoidAlgebra.lift k (DualNumber k) M (character (c • χ)) := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      ext <;> simp [character, OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale] <;> rfl
    · exact Subsingleton.elim _ _
  exact congrArg (fun f : MonoidAlgebra k M →ₐ[k] DualNumber k =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) h

theorem point_nat_scalar (χ : Additive M →+ k) (n : ℕ) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (n : k) ≫ point χ = point χ ^ n := by
  rw [point_scalar, Nat.cast_smul_eq_nsmul]
  exact congrArg Additive.toMul ((pointHom (k := k) (M := M)).map_nsmul n χ)

end

end OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents
