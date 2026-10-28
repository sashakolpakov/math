import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FixedPoints
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Field Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FieldFrobenius

noncomputable section

/-!
# IntegralComparison: the actual finite-field Frobenius is finite on finite-type affine charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C]

theorem integral : (FiniteField.frobeniusAlgHom k C).toRingHom.IsIntegral := by
  intro x
  refine ⟨Polynomial.X ^ Fintype.card k - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x (Fintype.card_pos.ne'), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  change x ^ Fintype.card k - x ^ Fintype.card k = 0
  exact sub_self _

variable [Algebra.FiniteType k C]

theorem finiteType : (FiniteField.frobeniusAlgHom k C).toRingHom.FiniteType := by
  have h : (FiniteField.frobeniusAlgHom k C).toRingHom.comp (algebraMap k C) = algebraMap k C :=
    RingHom.ext (FiniteField.frobeniusAlgHom k C).commutes
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k C)
  exact h.symm ▸ RingHom.finiteType_algebraMap.mpr inferInstance

theorem finite : (FiniteField.frobeniusAlgHom k C).toRingHom.Finite :=
  (integral k C).to_finite (finiteType k C)

theorem spec_finite : IsFinite (Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k C).toRingHom)) :=
  (IsFinite.SpecMap_iff _).mpr (finite k C)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FieldFrobenius
