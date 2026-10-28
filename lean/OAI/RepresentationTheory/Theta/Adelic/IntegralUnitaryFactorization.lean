import OAI.RepresentationTheory.Theta.Adelic.IntegralSpectralAvoidance
import OAI.RepresentationTheory.Theta.Adelic.IntegralModulus

/-! # Integral Unitary Factorization -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralUnitaryFactorization

noncomputable section

/-! Every integral unitary element is a product of two integral
unimodular open-cell elements when a sufficiently large integral
norm-one scalar family is available. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Adelic.IntegralSpectralAvoidance OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

section Scalar
variable {R J : Type*} [CommRing R] [StarRing R] [Fintype J] [DecidableEq J]

def scalarUnitary (H : Matrix J J R) (z : Rˣ) (hz : star z.val * z.val = 1) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H := by
  refine ⟨Units.map (Matrix.scalar J).toMonoidHom z, ?_⟩
  change (Matrix.scalar J z.val).conjTranspose * H * Matrix.scalar J z.val = H
  rw [Matrix.scalar_apply, Matrix.diagonal_conjTranspose]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change star z.val * H i j * z.val = H i j
  calc
    _ = (star z.val * z.val) * H i j := by ring
    _ = _ := by rw [hz, one_mul]

end Scalar

section Integral
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J] (T : Subring R)

omit [DecidableEq J] in
theorem matrix_product_integral {A B : Matrix J J R}
    (hA : ∀ i j, A i j ∈ T) (hB : ∀ i j, B i j ∈ T) : ∀ i j, (A * B) i j ∈ T := by
  intro i j
  exact T.sum_mem fun l _ => T.mul_mem (hA i l) (hB l j)

theorem scalar_matrix_integral {z : R} (hz : z ∈ T) : ∀ i j : J, Matrix.scalar J z i j ∈ T := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h, hz]

end Integral

variable {k I J : Type*} [Field k] [Fintype I] [Fintype J] [DecidableEq J]
variable (S : Subring k) [IsLocalRing S] (d : k) (hd : d ∈ S)
variable (H : Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))

def IntegralOpenCell (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H) : Prop :=
  ∃ u : (Matrix J J (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ, u.val = g.val.val - 1 ∧
    (∀ i j, u.val i j ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd) ∧
    (∀ i j, u.inv i j ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)

theorem integral_unitary_factorization (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H)
    (hg : ∀ i j, g.val.val i j ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)
    (z : I → (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ)
    (hz : ∀ i, star (z i).val * (z i).val = 1)
    (hzi : ∀ i, (z i).val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd ∧ (z i).inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)
    (hz1 : ∀ i, ∃ u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ, u.val = (z i).val - 1 ∧
      u.val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd ∧ u.inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)
    (hzd : ∀ i j, i ≠ j → ∃ u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ, u.val = (z i).val - (z j).val ∧
      u.val ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd ∧ u.inv ∈ QuadraticIntegralCoefficients.coefficientOrder S d hd)
    (hcard : 2 * Fintype.card J < Fintype.card I) :
    ∃ a b : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H, g = a * b ∧ IntegralOpenCell S d hd H a ∧ IntegralOpenCell S d hd H b := by
  let T := QuadraticIntegralCoefficients.coefficientOrder S d hd
  obtain ⟨i, u, hu, huv, hui⟩ := IntegralSpectralAvoidance.integral_spectral_avoidance S d hd g.val.val hg
    (fun i => (z i).val) (fun i => (hzi i).1) hzd hcard
  let b := scalarUnitary H (z i) (hz i)
  let a := g * b⁻¹
  have hb : ∀ j l, b.val.val j l ∈ T := scalar_matrix_integral T (hzi i).1
  have hbi : ∀ j l, b.val.inv j l ∈ T := scalar_matrix_integral T (hzi i).2
  refine ⟨a, b, by simp [a], ?_, ?_⟩
  · let U := -u * b.val⁻¹
    refine ⟨U, ?_, ?_, ?_⟩
    · change (-u.val) * (b⁻¹).val.val = g.val.val * (b⁻¹).val.val - 1
      have he : -u.val = g.val.val - b.val.val := by rw [hu, neg_sub]; rfl
      rw [he, sub_mul]
      have hb1 : b.val.val * (b⁻¹).val.val = 1 := b.val.val_inv
      rw [hb1]
    · exact matrix_product_integral T (fun j l => T.neg_mem (huv j l)) hbi
    · exact matrix_product_integral T hb (fun j l => T.neg_mem (hui j l))
  · obtain ⟨w, hw, hwv, hwi⟩ := hz1 i
    refine ⟨Units.map (Matrix.scalar J).toMonoidHom w, ?_, scalar_matrix_integral T hwv,
      scalar_matrix_integral T hwi⟩
    change Matrix.scalar J w.val = Matrix.scalar J (z i).val - 1
    rw [hw, map_sub, map_one]

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralUnitaryFactorization
