import OAI.AlgebraicGeometry.Resolution.Blowups.LabelledBoundaryMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates

/-! # Monomial Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Convert monomials in actual unit-scaled boundary labels to monomials in their displayed coordinates. -/

universe u v t

def Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents {ι : Type v} {σ : Type t} [Fintype ι]
    (r : ι → Option σ) (a : ι → ℕ) : σ → ℕ := by
  classical
  exact fun s => ∑ j, if r j = some s then a j else 0

theorem Boundary.MonomialCoordinates.Construction.partial_boundary_product_powers
    {R : Type u} [CommRing R] {ι : Type v} {σ : Type t} [Fintype ι] [Fintype σ]
    (r : ι → Option σ) (a : ι → ℕ) (x : σ → R) :
    (∏ j, (match r j with | none => 1 | some s => x s) ^ a j) =
      ∏ s, x s ^ Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents r a s := by
  classical
  have he (j : ι) : (match r j with | none => 1 | some s => x s) ^ a j =
      ∏ s, x s ^ (if r j = some s then a j else 0) := by
    cases h : r j with
    | none => simp
    | some s => simp
  simp_rw [he]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  exact Finset.prod_pow_eq_pow_sum Finset.univ _ (x s)

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundary_monomial_ideal
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (a : ι → ℕ) :
    Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} =
      (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := k) (Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a)}).map M.map := by
  classical
  let U := ∏ j, M.multiplier j ^ a j
  have hU : IsUnit U := IsUnit.prod_univ_iff.mpr (fun j => (M.multiplierUnit j).pow (a j))
  have hfactor : LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a =
      U * M.map (MonomialBlowupChart.Construction.coordinateMonomial (R := k) (Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a)) := by
    rw [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement]
    calc
      (∏ j, w j ^ a j) = ∏ j, M.multiplier j ^ a j * M.coordinateEquation j ^ a j := by
        apply Finset.prod_congr rfl
        intro j _
        rw [M.equation j, mul_pow]
        cases h : M.coordinate j <;> simp only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, h]
      _ = U * ∏ j, M.coordinateEquation j ^ a j := Finset.prod_mul_distrib
      _ = U * ∏ s, M.map (MvPolynomial.X s) ^ Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a s := by
        simp only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation]
        congr 1
        convert Boundary.MonomialCoordinates.Construction.partial_boundary_product_powers M.coordinate a (fun s => M.map (MvPolynomial.X s)) using 1
        apply Finset.prod_congr rfl
        intro j _
        cases M.coordinate j <;> rfl
      _ = U * M.map (MonomialBlowupChart.Construction.coordinateMonomial (R := k) (Boundary.MonomialCoordinates.Construction.partialBoundaryMonomialExponents M.coordinate a)) := by
        rw [MonomialBlowupChart.Construction.coordinateMonomial, map_prod]
        simp_rw [map_pow]
  rw [hfactor, Ideal.span_singleton_mul_left_unit hU, Ideal.map_span, Set.image_singleton]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
