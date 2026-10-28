import OAI.RepresentationTheory.Satake.Reduction
import OAI.RepresentationTheory.Satake.GL3TorusIwasawa

/-! # GL 3 GL -/

namespace OAI.RepresentationTheory.Satake.GL3GL.Core

noncomputable section

/-!
The concrete GL₃ local model and its normalized Satake map. The Borel is
the actual upper-triangular subgroup, the compact level is GL₃(O_F), and
the cocharacter lattice is ℤ³. The Iwasawa decomposition is proved by
integral column reduction. No multiplicativity or Satake isomorphism is
assumed in this construction.

This file establishes the normalized algebra homomorphism. Identification
of its image with the symmetric Laurent polynomials is a further theorem.
-/

open scoped Classical BigOperators

open _root_.Matrix ValuativeRel OAI.RepresentationTheory.Satake.Reduction.GeneralLinear

section Borel

variable (F : Type*) [Field F]

def upperBorel : Subgroup (Reduction.GeneralLinear.GL3 F) where
  carrier := {g | g.val.IsUpperTriangular}
  one_mem' := by
    intro i j hij
    have h : i ≠ j := ne_of_gt hij
    simp [h]
  mul_mem' := fun hg hh => hg.mul hh
  inv_mem' := by
    intro g hg
    let := g.invertible
    change (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

theorem diagonal_ne_zero (b : upperBorel F) (i : Fin 3) : b.val i i ≠ 0 := by
  have hdet := b.val.det_ne_zero
  rw [Matrix.det_of_isUpperTriangular b.property] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)

/-- The actual torus quotient of the upper-triangular Borel. -/
def diagonal : upperBorel F →* (Fin 3 → Fˣ) where
  toFun b i := Units.mk0 (b.val i i) (diagonal_ne_zero F b i)
  map_one' := by
    ext i
    change (1 : Matrix (Fin 3) (Fin 3) F) i i = 1
    simp
  map_mul' b c := by
    funext i
    apply Units.ext
    change (∑ j : Fin 3, b.val i j * c.val j i) = b.val i i * c.val i i
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · rw [b.property h, zero_mul]
      · rw [c.property h, mul_zero]
    · simp

end Borel

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

def integralLevel : Subgroup (Reduction.GeneralLinear.GL3 F) := (Reduction.GeneralLinear.integralMap (F := F)).range

def borelValuation : upperBorel F →* Multiplicative (Fin 3 → ℤ) :=
  (GL3TorusIwasawa.LocalTorus.latticeValuation F 3).comp (diagonal F)

theorem compact_borel_valuation (b : upperBorel F) (hb : b.val ∈ integralLevel F) :
    borelValuation F b = 1 := by
  obtain ⟨U, hU⟩ := hb
  have htri : U.val.IsUpperTriangular := by
    intro i j hij
    apply Subtype.val_injective
    have h := b.property hij
    rw [← hU] at h
    exact h
  have hunit (i : Fin 3) : IsUnit (U i i) := by
    have hdet := U.det.isUnit
    change IsUnit U.val.det at hdet
    rw [Matrix.det_of_isUpperTriangular htri] at hdet
    exact (IsUnit.prod_univ_iff.mp hdet) i
  apply Multiplicative.toAdd.injective
  funext i
  have hval : valuation F (b.val i i) = 1 := by
    rw [← hU]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation F))).mp (hunit i)
  exact congrArg Multiplicative.toAdd
    ((GL3TorusIwasawa.LocalTorus.exponent_eq_one_iff F (diagonal F b i)).mpr hval)

/-- The GL₃ Iwasawa decomposition is constructed from proved integral
column operations, with no factorization supplied as an assumption. -/
def decomposition : GL3TorusIwasawa.Iwasawa.Decomposition (integralLevel F) (Fin 3 → ℤ) where
  B := upperBorel F
  valuation := borelValuation F
  compact_valuation := compact_borel_valuation F
  factorization g := by
    obtain ⟨U, hU⟩ := Reduction.GeneralLinear.exists_integral_upperTriangular g
    refine ⟨⟨g * Reduction.GeneralLinear.integralMap U, hU⟩,
      ⟨Reduction.GeneralLinear.integralMap U⁻¹, ⟨U⁻¹, rfl⟩⟩, ?_⟩
    simp

def twoRho : (Fin 3 → ℤ) →+ ℤ where
  toFun ell := 2 * (ell 0 - ell 2)
  map_zero' := by simp
  map_add' x y := by simp; ring

def residueCardinality : ℕ := Nat.card (IsLocalRing.ResidueField (Reduction.GeneralLinear.O F))

theorem residueCardinality_pos : 0 < residueCardinality (F := F) :=
  Nat.card_pos

/-- The normalized Satake algebra homomorphism on the actual complex
spherical Hecke algebra of GL₃(F), with integral-level volume one. -/
def normalizedSatake :
    GL3TorusIwasawa.Iwasawa.algebra (integralLevel F) →ₐ[ℂ] AddMonoidAlgebra ℂ (Fin 3 → ℤ) :=
  GL3TorusIwasawa.Normalization.satake (decomposition F) (residueCardinality (F := F))
    (residueCardinality_pos F) twoRho

theorem normalizedSatake_coeff
    (T : GL3TorusIwasawa.Iwasawa.algebra (integralLevel F)) (ell : Fin 3 → ℤ) :
    (normalizedSatake F T).coeff ell =
      ((decomposition F).constantTerm T).coeff ell *
        (residueCardinality (F := F) : ℂ) ^ (ell 2 - ell 0) := by
  rw [normalizedSatake, GL3TorusIwasawa.Normalization.satake_coeff]
  congr 1
  have hs : (Real.sqrt (residueCardinality (F := F) : ℝ) : ℂ) ^ (2 : ℤ) =
      (residueCardinality (F := F) : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  rw [← hs, ← _root_.zpow_mul]
  congr 1
  simp [twoRho]
  ring

end

end OAI.RepresentationTheory.Satake.GL3GL.Core
