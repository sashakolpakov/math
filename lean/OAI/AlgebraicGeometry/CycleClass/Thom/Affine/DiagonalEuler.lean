import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalSequence

/-! # Diagonal Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEuler.Constructions

noncomputable section

/-! Reduction to the diagonal for the actual geometric affine stalk
quotients and actual coordinate-difference section germs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions.Prime OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.CoordinateMaps
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalDiagonalEuler OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [LocallyOfFiniteType X.hom]
  (A B : IrreducibleCloseds X.left) (x : X.left) (hxA : x ∈ (A : Set X.left)) (hxB : x ∈ (B : Set X.left))

omit [LocallyOfFiniteType X.hom] in
theorem affine_support_euler (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (X.left.presheaf.stalk x) (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X.left A x hxA))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X.left B x hxB)) d =
    TorAlgebra.Euler.Tor.euler (Localization.AtPrime (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x).asIdeal)
      (TorAlgebra.LocalDiagonalEuler.localizedQuotient Γ(X.left, ⊤) (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal)
      (TorAlgebra.LocalDiagonalEuler.localizedQuotient Γ(X.left, ⊤) (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x) (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint B)).asIdeal) d := by
  have h := Local.QuotientEulerEquiv.Constructions.euler_quotients_ringEquiv (X.left.presheaf.stalk x)
    (Localization.AtPrime (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x).asIdeal) (PairSupportKernel.Constructions.affineSupportStalkIso X x).commRingCatIsoToRingEquiv
    (StalkPrimeQuotient.Constructions.kernelPrime X.left A x hxA).asIdeal (StalkPrimeQuotient.Constructions.kernelPrime X.left B x hxB).asIdeal d
  exact h.trans (Local.QuotientEulerEquiv.Constructions.euler_quotients_congr _ _ _ _ _
    (PairSupportKernel.Constructions.affine_support_kernel X A x hxA) (PairSupportKernel.Constructions.affine_support_kernel X B x hxB) d)

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

omit [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem affine_diagonal_euler_coordinates (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (DiagonalEquations.Constructions.productLocalRing X x)
      (ModuleCat.of _ ((DiagonalEquations.Constructions.productLocalRing X x) ⧸ Ideal.ofList (DiagonalEquations.Constructions.coordinateDifferenceGerms X n x)))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing (pullback X.hom X.hom) (PairSupportKernel.Constructions.Prime.affinePairSupport X X A B)
        (pullback.diagonal X.hom x) (PairSupportKernel.Constructions.diagonal_mem_affinePairSupport X A B x hxA hxB))) d =
    TorAlgebra.Euler.Tor.euler (Localization.AtPrime (DiagonalStalk.Constructions.diagonalCoordinatePrime X x).asIdeal)
      (ModuleCat.of _ ((Localization.AtPrime (DiagonalStalk.Constructions.diagonalCoordinatePrime X x).asIdeal) ⧸
        Ideal.ofList (Local.PolynomialDiagonalIdeal.Constructions.localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x))))
      (TorAlgebra.LocalDiagonalEuler.localizedQuotient (Γ(X.left, ⊤) ⊗[ℂ] Γ(X.left, ⊤)) (DiagonalStalk.Constructions.diagonalCoordinatePrime X x) (PairSupportKernel.Constructions.Prime.affinePairIdeal X X A B)) d := by
  have h := Local.QuotientEulerEquiv.Constructions.euler_quotients_ringEquiv (DiagonalEquations.Constructions.productLocalRing X x)
    (Localization.AtPrime (DiagonalStalk.Constructions.diagonalCoordinatePrime X x).asIdeal) (DiagonalStalk.Constructions.diagonalStalkIso X x).commRingCatIsoToRingEquiv
    (Ideal.ofList (DiagonalEquations.Constructions.coordinateDifferenceGerms X n x))
    (StalkPrimeQuotient.Constructions.kernelPrime (pullback X.hom X.hom) (PairSupportKernel.Constructions.Prime.affinePairSupport X X A B) (pullback.diagonal X.hom x)
      (PairSupportKernel.Constructions.diagonal_mem_affinePairSupport X A B x hxA hxB)).asIdeal d
  have hI : (Ideal.ofList (DiagonalEquations.Constructions.coordinateDifferenceGerms X n x)).map (DiagonalStalk.Constructions.diagonalStalkIso X x).hom.hom =
      Ideal.ofList (Local.PolynomialDiagonalIdeal.Constructions.localEquations ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x)) := by
    rw [Ideal.map_ofList, DiagonalEquations.Constructions.coordinateDifferenceGerms_map]
    rfl
  exact h.trans (Local.QuotientEulerEquiv.Constructions.euler_quotients_congr _ _ _ _ _ hI (PairSupportKernel.Constructions.affine_pair_support_kernel X A B x hxA hxB) d)

theorem affine_diagonal_euler
    [Algebra.FormallyUnramified (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsNoetherianRing (Γ(X.left, ⊤) ⊗[MvPolynomial (Fin n) ℂ] Γ(X.left, ⊤))] (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (X.left.presheaf.stalk x) (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X.left A x hxA))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X.left B x hxB)) d =
    TorAlgebra.Euler.Tor.euler (DiagonalEquations.Constructions.productLocalRing X x)
      (ModuleCat.of _ ((DiagonalEquations.Constructions.productLocalRing X x) ⧸ Ideal.ofList (DiagonalEquations.Constructions.coordinateDifferenceGerms X n x)))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing (pullback X.hom X.hom) (PairSupportKernel.Constructions.Prime.affinePairSupport X X A B)
        (pullback.diagonal X.hom x) (PairSupportKernel.Constructions.diagonal_mem_affinePairSupport X A B x hxA hxB))) d :=
  (affine_support_euler X A B x hxA hxB d).trans
    ((TorAlgebra.LocalDiagonalSequence.euler_eq_sequence ℂ Γ(X.left, ⊤) n (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X x)
      (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint A)).asIdeal (ProductIs.Constructions.CoordinateMaps.affineCoordinateMap X (IntersectionGeometry.supportPoint B)).asIdeal d).trans
        (affine_diagonal_euler_coordinates X A B x hxA hxB n d).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEuler.Constructions
