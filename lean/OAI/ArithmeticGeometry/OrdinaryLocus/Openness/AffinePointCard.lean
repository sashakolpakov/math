import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteRationalPoints
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Affine Point Card -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffinePointCard.Construction

noncomputable section

/-! Bounding rational point counts by the rank of an affine coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def specPointsEquivAlgHom
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≃ (B →ₐ[R] C) where
  toFun f :=
    { toRingHom := (Spec.preimage f.left).hom
      commutes' := fun r => by
        have hw : f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
            Spec.map (CommRingCat.ofHom (algebraMap R C)) := f.w
        have h := congrArg Spec.preimage hw
        simp only [Spec.preimage_comp, Spec.preimage_map] at h
        exact congrArg (fun f => f.hom r) h }
  invFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)
  left_inv f := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage f.left
  right_inv f := by
    apply AlgHom.ext
    intro x
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))) x = f x
    rw [Spec.preimage_map]
    rfl

def specRationalPointsEquivAlgHom
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (Over.mk (𝟙 (Spec (.of R))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≃ (B →ₐ[R] R) := by
  simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using
    specPointsEquivAlgHom R B R

/-- Distinct algebra characters are linearly independent, so their number
cannot exceed the coordinate algebra's dimension. -/
theorem card_algHom_le_finrank
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B] :
    Nat.card (B →ₐ[K] K) ≤ Module.finrank K B := by
  cases finite_or_infinite (B →ₐ[K] K) with
  | inl h =>
    let := Fintype.ofFinite (B →ₐ[K] K)
    have hcard := (linearIndependent_algHom_toLinearMap K B K).fintype_card_le_finrank
    simpa only [Subspace.dual_finrank_eq, Nat.card_eq_fintype_card] using hcard
  | inr h => simp only [Nat.card_eq_zero_of_infinite, Nat.zero_le]

theorem card_specRationalPoints_le_finrank
    (K B : Type u) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B] :
    Nat.card (Over.mk (𝟙 (Spec (.of K))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))) ≤ Module.finrank K B :=
  (Nat.card_congr (specRationalPointsEquivAlgHom K B)).trans_le (card_algHom_le_finrank K B)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffinePointCard.Construction
