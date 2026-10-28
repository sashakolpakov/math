import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBasisLattice
import OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Position Lattices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PositionLattices.TestTransport

noncomputable section

/-! Rational position coordinates identify finite-adelic lattice cosets
on their rational points. Both sides use their original integral lattices. -/

open scoped Classical _root_.NumberField

open _root_.NumberField OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TotallyRealData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K)

theorem rationalPositionCoordinates_scaled_integral_iff (q : ℚ)
    (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    (∀ i, ∃ z : ℤ, q * (z : ℚ) = RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i) ↔
      ∀ j, ∃ r : 𝓞 F, algebraMap ℚ F q * algebraMap (𝓞 F) F r = x j := by
  have hc (i : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) : RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i =
      (integralBasis F).equivFun (x (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.frameCoefficientEquiv A i).1)
        (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.frameCoefficientEquiv A i).2 := rfl
  constructor
  · intro h j
    apply (IntegralBasisLattice.TestTransport.integralBasis_scaled_integral_iff F q (x j)).mp
    intro i
    have hi := h ((RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.frameCoefficientEquiv A).symm (j, i))
    simpa only [hc, Equiv.apply_symm_apply] using hi
  · intro h i
    rw [hc]
    exact (IntegralBasisLattice.TestTransport.integralBasis_scaled_integral_iff F q _).mpr
      (h (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.frameCoefficientEquiv A i).1) (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.frameCoefficientEquiv A i).2

theorem rational_mem_finiteLattice_iff {ι : Type*} (q : ℚ) (hq : q ≠ 0)
    (x : ι → ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔ ∀ i, ∃ z : ℤ, q * (z : ℚ) = x i := by
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_mem_iff]
  change (∀ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q⁻¹ * algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (x i) ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele) ↔ _
  simp only [← map_mul, RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff]
  apply forall_congr'
  intro i
  apply exists_congr
  intro z
  constructor
  · intro hz
    rw [hz, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  · intro hz
    rw [← hz, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

theorem rationalPositionCoordinates_lattice_iff (q : ℚ) (hq : q ≠ 0)
    (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x ∈ RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (algebraMap ℚ F q)
        ((map_ne_zero (algebraMap ℚ F)).mpr hq) := by
  rw [rational_mem_finiteLattice_iff, rationalPositionCoordinates_scaled_integral_iff]
  exact (RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff _ _ x).symm

theorem rationalPositionCoordinates_coset_iff (q : ℚ) (hq : q ≠ 0)
    (a x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x) -
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A a) ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq ↔
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a ∈
        RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (algebraMap ℚ F q)
          ((map_ne_zero (algebraMap ℚ F)).mpr hq) := by
  have hQ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A (x - a)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x) -
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A a) := by
    funext i
    simp only [map_sub, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal, Pi.sub_apply]
  have hF : RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (x - a) =
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a := by
    funext i
    simp only [RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition, Pi.sub_apply, map_sub]
  rw [← hQ, ← hF]
  exact rationalPositionCoordinates_lattice_iff A q hq (x - a)

theorem rationalPositionCoordinates_coset_value (q : ℚ) (hq : q ≠ 0)
    (a x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator q hq (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A a))
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) =
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator (algebraMap ℚ F q)
        ((map_ne_zero (algebraMap ℚ F)).mpr hq) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition a)
        (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  simp only [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator, RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator,
    RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionIndicator, Set.indicator, SetLike.mem_coe,
    rationalPositionCoordinates_coset_iff]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PositionLattices.TestTransport
