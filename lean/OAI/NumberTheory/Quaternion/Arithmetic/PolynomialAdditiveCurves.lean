import OAI.NumberTheory.Quaternion.Arithmetic.UnipotentOneParameter
import Mathlib.Topology.Algebra.Polynomial

/-! # Polynomial Additive Curves -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PolynomialAdditiveCurves

noncomputable section

/-! Polynomial additive curves defined over the ground field, with their
compatible points over every extension field. -/

open scoped Classical

variable {F : Type} [Field F] {n : ℕ}

structure PolynomialAdditiveCurve (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) where
  coordinates : Matrix (Fin n) (Fin n) (Polynomial F)
  hom : (K : Type) → [Field K] → (ρ : F →+* K) → (Multiplicative K →* G.Points ρ)
  coordinate_eq : ∀ (K : Type) [Field K] (ρ : F →+* K) (t : K) (i j : Fin n),
    PolynomialGaloisNorm.matrixPointsHom G ρ (hom K ρ (Multiplicative.ofAdd t)) i j =
      (coordinates i j).eval₂ ρ t

namespace PolynomialAdditiveCurve

variable {G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n} (u : PolynomialAdditiveCurve G)

theorem map_point {K L : Type} [Field K] [Field L] (ρ : F →+* K) (σ : K →+* L) (t : K) :
    G.map ρ σ (u.hom K ρ (Multiplicative.ofAdd t)) =
      u.hom L (σ.comp ρ) (Multiplicative.ofAdd (σ t)) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change σ (PolynomialGaloisNorm.matrixPointsHom G ρ (u.hom K ρ (Multiplicative.ofAdd t)) i j) = _
  rw [u.coordinate_eq]
  change _ = PolynomialGaloisNorm.matrixPointsHom G (σ.comp ρ) (u.hom L (σ.comp ρ) (Multiplicative.ofAdd (σ t))) i j
  rw [u.coordinate_eq]
  exact Polynomial.hom_eval₂ _ _ _ _

theorem continuous_point {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (ρ : F →+* K) : Continuous (fun t : K => u.hom K ρ (Multiplicative.ofAdd t)) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  change Continuous (fun t : K => PolynomialGaloisNorm.matrixPointsHom G ρ (u.hom K ρ (Multiplicative.ofAdd t)) i j)
  simp only [u.coordinate_eq]
  exact (u.coordinates i j).continuous_eval₂ ρ

end PolynomialAdditiveCurve

variable [CharZero F]

omit [CharZero F] in
theorem polynomial_curve_hom_of_nat_powers (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    {K : Type} [Field K] [CharZero K] (ρ : F →+* K)
    (P : Matrix (Fin n) (Fin n) (Polynomial K)) (g : G.Points ρ)
    (hP : ∀ m : ℕ, PolynomialMatrixCurves.evalPolynomialMatrix P (m : K) = PolynomialGaloisNorm.matrixPointsHom G ρ g ^ m) :
    ∃ u : Multiplicative K →* G.Points ρ,
      ∀ t : K, PolynomialGaloisNorm.matrixPointsHom G ρ (u (Multiplicative.ofAdd t)) = PolynomialMatrixCurves.evalPolynomialMatrix P t := by
  have hNat (m : ℕ) : ∃ g₀ : G.Points ρ, PolynomialGaloisNorm.matrixPointsHom G ρ g₀ = PolynomialMatrixCurves.evalPolynomialMatrix P (m : K) := by
    refine ⟨g ^ m, ?_⟩
    rw [map_pow, hP]
  choose q hq using PolynomialCurveGroupPoints.polynomial_curve_mem_group_of_nat G ρ P hNat
  refine ⟨{ toFun a := q a.toAdd, map_one' := ?_, map_mul' := ?_ }, hq⟩
  · apply PolynomialGaloisNorm.matrixPointsHom_injective G ρ
    change PolynomialGaloisNorm.matrixPointsHom G ρ (q 0) = PolynomialGaloisNorm.matrixPointsHom G ρ 1
    rw [map_one, hq]
    simpa only [Nat.cast_zero, pow_zero] using hP 0
  · intro a b
    apply PolynomialGaloisNorm.matrixPointsHom_injective G ρ
    change PolynomialGaloisNorm.matrixPointsHom G ρ (q (a.toAdd + b.toAdd)) = PolynomialGaloisNorm.matrixPointsHom G ρ (q a.toAdd * q b.toAdd)
    rw [map_mul, hq, hq, hq]
    exact PolynomialMatrixCurves.polynomialMatrix_add_law_of_nat_powers P (PolynomialGaloisNorm.matrixPointsHom G ρ g) hP a.toAdd b.toAdd

theorem unipotent_point_has_polynomialAdditiveCurve (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (g : G.RationalPoints) (hg : IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g - 1)) :
    ∃ u : PolynomialAdditiveCurve G, u.hom F (RingHom.id F) (Multiplicative.ofAdd 1) = g := by
  obtain ⟨P, hP⟩ := PolynomialMatrixCurves.unipotent_has_polynomial_powers (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g) hg
  have hK (K : Type) [Field K] (ρ : F →+* K) :
      ∃ u : Multiplicative K →* G.Points ρ,
        ∀ t : K, PolynomialGaloisNorm.matrixPointsHom G ρ (u (Multiplicative.ofAdd t)) =
          PolynomialMatrixCurves.evalPolynomialMatrix (P.map (Polynomial.map ρ)) t := by
    let : CharZero K := charZero_of_injective_ringHom ρ.injective
    apply polynomial_curve_hom_of_nat_powers G ρ _ (G.map (RingHom.id F) ρ g)
    intro m
    have he : PolynomialMatrixCurves.evalPolynomialMatrix (P.map (Polynomial.map ρ)) (m : K) =
        (PolynomialMatrixCurves.evalPolynomialMatrix P (m : F)).map ρ := by
      apply Matrix.ext
      intro i j
      change ((P i j).map ρ).eval (m : K) = ρ ((P i j).eval (m : F))
      rw [← map_natCast ρ m, Polynomial.eval_map_apply]
    rw [he, hP]
    exact map_pow ρ.mapMatrix _ m
  choose u hu using hK
  let c : PolynomialAdditiveCurve G := {
    coordinates := P
    hom := u
    coordinate_eq K _ ρ t i j := by
      rw [hu]
      exact Polynomial.eval_map ρ t }
  refine ⟨c, ?_⟩
  apply PolynomialGaloisNorm.matrixPointsHom_injective G (RingHom.id F)
  apply Matrix.ext
  intro i j
  rw [c.coordinate_eq]
  change (P i j).eval 1 = _
  have he := congrFun (congrFun (hP 1) i) j
  simpa only [Nat.cast_one, pow_one] using! he

end

end OAI.NumberTheory.Quaternion.Arithmetic.PolynomialAdditiveCurves
