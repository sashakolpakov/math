import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorEquiv
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.DualPairing
import OAI.AlgebraicGeometry.Comparison.Betti.Pure.OneCovectorDual
import OAI.AlgebraicGeometry.Comparison.Betti.IteratedCovectorDeterminant

/-! # Covector Exterior Basis -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorBasis.Holomorphic

noncomputable section

/-! Exterior products of a complex cotangent basis give actual pure covector bases, with the original wedge normalization. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def exteriorDualPureCovectorEquiv (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] (n : ℕ) :
    (⋀[ℂ]^n (Module.Dual ℂ E)) ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 :=
  (Exterior.DualPairing.LinearAlgebra.exteriorDualPairingEquiv (Module.finBasis ℂ E) n).trans
    (CovectorExteriorEquiv.Holomorphic.pureCovectorExteriorDualEquiv E n).symm

theorem exteriorDualPureCovectorEquiv_normalization (n : ℕ) (a : ⋀[ℂ]^n (Module.Dual ℂ E)) :
    CovectorExteriorDual.Holomorphic.pureCovectorExteriorDualMap E n (exteriorDualPureCovectorEquiv E n a) =
      exteriorPower.pairingDual ℂ E n a := by
  change CovectorExteriorEquiv.Holomorphic.pureCovectorExteriorDualEquiv E n
    ((CovectorExteriorEquiv.Holomorphic.pureCovectorExteriorDualEquiv E n).symm
      (Exterior.DualPairing.LinearAlgebra.exteriorDualPairingEquiv (Module.finBasis ℂ E) n a)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun L => L a)
    (Exterior.DualPairing.LinearAlgebra.exteriorDualPairingEquiv_toLinearMap (Module.finBasis ℂ E) n)

variable {ι : Type} [LinearOrder ι]

def pureCovectorExteriorBasis (b : Module.Basis ι ℂ (Module.Dual ℂ E)) (n : ℕ) :
    Module.Basis (Set.powersetCard ι n) ℂ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) :=
  (b.exteriorPower n).map (exteriorDualPureCovectorEquiv E n)

theorem pureCovectorExteriorBasis_apply_det (b : Module.Basis ι ℂ (Module.Dual ℂ E)) (n : ℕ)
    (s : Set.powersetCard ι n) (v : Fin n → E) :
    (pureCovectorExteriorBasis b n s).val v =
      (Matrix.of (fun i j => b (Set.powersetCard.ofFinEmbEquiv.symm s j) (v i))).det := by
  change (exteriorDualPureCovectorEquiv E n (b.exteriorPower n s)).val v = _
  rw [← CovectorExteriorDual.Holomorphic.pureCovectorExteriorDualMap_apply E n _ v,
    exteriorDualPureCovectorEquiv_normalization, exteriorPower.basis_apply]
  exact exteriorPower.pairingDual_ιMulti_ιMulti _ _

theorem pureCovectorExteriorBasis_eq_iteratedWedge (b : Module.Basis ι ℂ (Module.Dual ℂ E)) (n : ℕ)
    (s : Set.powersetCard ι n) :
    (pureCovectorExteriorBasis b n s).val = AlternatingCovectors.Smooth.iteratedCovectorWedge n 1
      (fun j => ((OneCovectorDual.Holomorphic.pureOneCovectorDualEquiv E).symm
        (b (Set.powersetCard.ofFinEmbEquiv.symm s j))).val) := by
  ext v
  rw [pureCovectorExteriorBasis_apply_det, IteratedCovectorDeterminant.Smooth.iteratedCovectorWedge_eq_det, one_mul]
  congr 1

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorExteriorBasis.Holomorphic
