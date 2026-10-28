import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.LogarithmicTangentComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates

/-! # Tangent Carrier Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.TangentCarrierComparison.Construction

noncomputable section

/-! A labelled boundary model and logarithmic normal derivations construct the native tangent comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_modeled_tangent_carrier_comparison
    {R β : Type} [CommRing R] [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    (w : β → R) (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ R β w) (J : Ideal R) (z t : R) (n : ℕ)
    (p : PrimeSpectrum R) (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n ≤ p.asIdeal)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n) (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)
    (D E : Derivation ℂ R R) (hDz : D z = 1) (hEt : E t = 1)
    (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ w) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ w) :
    Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n))
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t}))
      (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i})) n p) := by
  let : Algebra (MvPolynomial M.indices ℂ) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices ℂ) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower ℂ (MvPolynomial M.indices ℂ) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  have hDB : ∀ i ∈ M.boundaryIndices, D (algebraMap (MvPolynomial M.indices ℂ) R (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial M.indices ℂ) R (MvPolynomial.X i)} := by
    rw [M.logarithmic_coordinates] at hD
    exact fun i hi => hD ⟨i, hi⟩
  have hEB : ∀ i ∈ M.boundaryIndices, E (algebraMap (MvPolynomial M.indices ℂ) R (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial M.indices ℂ) R (MvPolynomial.X i)} := by
    rw [M.logarithmic_coordinates] at hE
    exact fun i hi => hE ⟨i, hi⟩
  obtain ⟨A⟩ := Affine.LogarithmicTangentComparison.Construction.exists_affine_tangent_carrier_comparison_of_logarithmic_derivations J M.boundaryIndices
    z t n p hp hz ht D E hDz hEt hDB hEB
  refine ⟨{ ambient := A.ambient
            left := A.left
            right := A.right
            left_etale := A.left_etale
            right_etale := A.right_etale
            ground := A.ground
            ideal := A.ideal
            carrier := A.carrier
            boundary := ?_
            congruence := A.congruence
            point := A.point
            point_eq := A.point_eq }⟩
  intro i
  rw [M.component_ideal i]
  cases hi : M.coordinate i with
  | none => simp only [DifferentialUnitGluing.Construction.affineQuotientKernel_top, Scheme.IdealSheafData.comap_top]
  | some s => exact A.boundary ⟨s, (M.mem_boundaryIndices s).mpr ⟨i, hi⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.TangentCarrierComparison.Construction
