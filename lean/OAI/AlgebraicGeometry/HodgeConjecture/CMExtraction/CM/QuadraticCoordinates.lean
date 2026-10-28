import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase
import Mathlib.NumberTheory.NumberField.CMField

/-! # Quadratic Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuadraticCoordinates

noncomputable section

/-! Explicit quadratic coordinates for a CM field over its maximal real
subfield, using the actual nonzero imaginary coefficient. -/

open _root_.NumberField OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev realBase := maximalRealSubfield E

def squareParameter (δ : E) (hδ : IsCMField.complexConj E δ = -δ) : realBase E :=
  ⟨δ ^ 2, (IsCMField.complexConj_eq_self_iff E _).mp (by simp [hδ])⟩

def evaluation (δ : E) (hδ : IsCMField.complexConj E δ = -δ) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ) →ₐ[realBase E] E :=
  QuadraticAlgebra.lift ⟨δ, by
    change δ * δ = δ ^ 2 * 1 + 0 * δ
    ring⟩

theorem evaluation_apply (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ)) :
    evaluation E δ hδ z = (z.re : E) + (z.im : E) * δ := by
  change (z.re : E) * 1 + (z.im : E) * δ = (z.re : E) + (z.im : E) * δ
  rw [mul_one]

def realCoordinate (x : E) : realBase E :=
  ⟨(x + IsCMField.complexConj E x) / 2,
    (IsCMField.complexConj_eq_self_iff E _).mp (by
      simp only [map_div₀, map_add, map_ofNat, IsCMField.complexConj_apply_apply]
      ring)⟩

def imaginaryCoordinate (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (x : E) : realBase E :=
  ⟨(x - IsCMField.complexConj E x) / (2 * δ),
    (IsCMField.complexConj_eq_self_iff E _).mp (by
      simp only [map_div₀, map_sub, map_mul, map_ofNat, hδ, IsCMField.complexConj_apply_apply,
        mul_neg, div_neg, ← neg_div, neg_sub])⟩

def coordinates (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (x : E) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ) :=
  ⟨realCoordinate E x, imaginaryCoordinate E δ hδ x⟩

theorem evaluation_coordinates (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (x : E) : evaluation E δ hδ (coordinates E δ hδ x) = x := by
  rw [evaluation_apply]
  change (x + IsCMField.complexConj E x) / 2 +
    (x - IsCMField.complexConj E x) / (2 * δ) * δ = x
  field_simp
  ring

theorem coordinates_evaluation (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ)) :
    coordinates E δ hδ (evaluation E δ hδ z) = z := by
  rw [evaluation_apply]
  ext
  · change ((z.re : E) + (z.im : E) * δ +
      IsCMField.complexConj E ((z.re : E) + (z.im : E) * δ)) / 2 = (z.re : E)
    simp only [map_add, map_mul, IsCMField.complexConj_apply_eq_self, hδ]
    ring
  · change ((z.re : E) + (z.im : E) * δ -
      IsCMField.complexConj E ((z.re : E) + (z.im : E) * δ)) / (2 * δ) = (z.im : E)
    simp only [map_add, map_mul, IsCMField.complexConj_apply_eq_self, hδ]
    field_simp
    ring

def quadraticEquiv (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ) ≃ₐ[realBase E] E :=
  AlgEquiv.ofBijective (evaluation E δ hδ)
    ⟨Function.LeftInverse.injective (coordinates_evaluation E δ hδ hδ0),
      Function.RightInverse.surjective (evaluation_coordinates E δ hδ hδ0)⟩

theorem squareParameter_ne_zero (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    squareParameter E δ hδ ≠ 0 := by
  intro h
  exact pow_ne_zero 2 hδ0 (congrArg (fun x : realBase E => (x : E)) h)

theorem squareParameter_not_isSquare (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    ¬IsSquare (squareParameter E δ hδ) := by
  rintro ⟨r, hr⟩
  have hs : δ ^ 2 = (r : E) ^ 2 := by
    have h := congrArg (fun x : realBase E => (x : E)) hr
    simpa only [squareParameter, Subfield.coe_mul, pow_two] using h
  have hf : IsCMField.complexConj E δ = δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he <;> simp [he]
  have hh : δ = -δ := hf.symm.trans hδ
  apply hδ0
  linear_combination (1 / 2 : E) * hh

theorem evaluation_conjugate (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ)) :
    evaluation E δ hδ (star z) = IsCMField.complexConj E (evaluation E δ hδ z) := by
  rw [evaluation_apply, evaluation_apply]
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, zero_mul, add_zero,
    Subfield.coe_neg, map_add, map_mul, IsCMField.complexConj_apply_eq_self, hδ]
  ring

theorem quadraticEquiv_conjugate (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (realBase E) (squareParameter E δ hδ)) :
    quadraticEquiv E δ hδ hδ0 (star z) = IsCMField.complexConj E (quadraticEquiv E δ hδ hδ0 z) :=
  evaluation_conjugate E δ hδ z

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuadraticCoordinates
