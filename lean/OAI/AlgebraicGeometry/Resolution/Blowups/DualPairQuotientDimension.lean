import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Dual Pair Quotient Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DualPairQuotientDimension.Construction

noncomputable section

/-! Successive normal equations give the actual smooth quotient and its dimension drop. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

def normalPreservingQuotientDerivation (E : Derivation k R R) (z : R) (hz : E z = 0) :
    Derivation k (R ⧸ Ideal.span {z}) (R ⧸ Ideal.span {z}) :=
  Coordinate.Regularity.Construction.quotientDerivation E (Ideal.span {z}) (by
    intro x hx
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hx
    rw [ht, E.leibniz, hz]
    change z * E t + t * 0 ∈ Ideal.span {z}
    rw [mul_zero, add_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z))

theorem normalPreservingQuotientDerivation_mk (E : Derivation k R R) (z : R) (hz : E z = 0) (g : R) :
    normalPreservingQuotientDerivation E z hz (Ideal.Quotient.mk (Ideal.span {z}) g) =
      Ideal.Quotient.mk (Ideal.span {z}) (E g) := rfl

theorem normal_pair_quotient_map (z g : R) :
    (Ideal.span {z, g}).map (Ideal.Quotient.mk (Ideal.span {z})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {z}) g} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
  exact Ideal.span_insert_zero

theorem transverse_pair_quotient_smooth [Algebra.Smooth k R]
    (z g : R) (D E : Derivation k R R) (hDz : D z = 1) (hEz : E z = 0) (hEg : E g = 1) :
    Algebra.Smooth k (R ⧸ Ideal.span {z, g}) := by
  let Q := R ⧸ Ideal.span {z}
  let : Algebra.Smooth k Q := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hDz
  let δ := normalPreservingQuotientDerivation E z hEz
  have hδ : δ (Ideal.Quotient.mk (Ideal.span {z}) g) = 1 := by
    rw [normalPreservingQuotientDerivation_mk, hEg, map_one]
  let : Algebra.Smooth k (Q ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {z}) g}) :=
    Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one δ _ hδ
  let : Algebra.Smooth k (Q ⧸ (Ideal.span {z, g}).map (Ideal.Quotient.mkₐ k (Ideal.span {z}))) := by
    change Algebra.Smooth k (Q ⧸ (Ideal.span {z, g}).map (Ideal.Quotient.mk (Ideal.span {z})))
    rw [normal_pair_quotient_map]
    infer_instance
  exact Algebra.Smooth.of_equiv (DoubleQuot.quotQuotEquivQuotOfLEₐ k
    (show Ideal.span {z} ≤ Ideal.span {z, g} from Ideal.span_mono (by simp)))

theorem transverse_pair_quotient_dimension [Algebra ℚ R] [IsNoetherianRing R]
    (z g : R) (D E : Derivation k R R) (hDz : D z = 1) (hEz : E z = 0) (hEg : E g = 1)
    (d : ℕ) (hd : ringKrullDim R ≤ (d + 2 : ℕ)) :
    ringKrullDim (R ⧸ Ideal.span {z, g}) ≤ d := by
  let Q := R ⧸ Ideal.span {z}
  have hdQ : ringKrullDim Q ≤ (d + 1 : ℕ) := NormalQuotientDimension.Construction.normal_quotient_dimension_induction D z hDz (d + 1) hd
  let δ := normalPreservingQuotientDerivation E z hEz
  have hδ : δ (Ideal.Quotient.mk (Ideal.span {z}) g) = 1 := by
    rw [normalPreservingQuotientDerivation_mk, hEg, map_one]
  have hd' := NormalQuotientDimension.Construction.normal_quotient_dimension_induction δ _ hδ d hdQ
  have hmap := normal_pair_quotient_map z g
  rw [← hmap] at hd'
  exact (DoubleQuot.quotQuotEquivQuotOfLE
    (show Ideal.span {z} ≤ Ideal.span {z, g} from Ideal.span_mono (by simp))).ringKrullDim.symm.le.trans hd'

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DualPairQuotientDimension.Construction
