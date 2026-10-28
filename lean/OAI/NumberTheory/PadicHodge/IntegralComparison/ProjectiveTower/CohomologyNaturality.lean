import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.Duality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TowerCechPositiveNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.IsoIndexTransport

/-! # Cohomology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.CohomologyNaturality

noncomputable section

/-! The complementary-cohomology coordinates of a projective kernel
tower respect the literal maps of towers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {T T' : KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)}
  [∀ i, (T.object i).IsQuasicoherent] [∀ i, (T'.object i).IsQuasicoherent]
  [∀ i, (T.term i).IsQuasicoherent] [∀ i, (T'.term i).IsQuasicoherent]
  (a : KernelTowerMap.Hom T T') (n : ℕ) (hn : Fintype.card σ = n + 2)
  (hT : ∀ q < n + 1, ∀ i, IsZero ((TopCechRightExact.functor
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q).obj (T.term i)))
  (hT' : ∀ q < n + 1, ∀ i, IsZero ((TopCechRightExact.functor
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q).obj (T'.term i)))

omit [IsNoetherianRing R] in
@[reassoc]
theorem naturality (d : ℕ) (hd : d ≤ n + 1) :
    HomologicalComplex.homologyMap (KernelTowerCechNaturality.complexMap
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) a (n + 1)) d ≫
        (Duality.cohomologyIso T' n hn hT' d hd).hom =
      (Duality.cohomologyIso T n hn hT d hd).hom ≫
        (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1 - d)).map (a.object 0) := by
  cases d with
  | zero =>
    change HomologicalComplex.homologyMap (KernelTowerCechNaturality.complexMap
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) a (n + 1)) 0 ≫
        (Duality.zeroIso T' n hn).hom =
      (Duality.zeroIso T n hn).hom ≫
        (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1)).map (a.object 0)
    exact
      KernelTowerCechNaturality.zero (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
        a (n + 1) (by simpa using hn.le)
  | succ i =>
    have hi : i ≤ n := by omega
    have hi' : n - i + i = n := Nat.sub_add_cancel hi
    exact IsoIndexTransport.naturality
      (fun r => HomologicalComplex.homologyMap (KernelTowerCechNaturality.complexMap
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) a r) (i + 1))
      (fun r => (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) r).map (a.object 0))
      (show n + 1 = n - i + i + 1 by omega)
      (show n - i = n + 1 - (i + 1) by omega)
      (KernelTowerCechHomology.shiftedPositiveIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
        T (n - i) i (by simpa [hi'] using hn.le) (fun q hq j => hT q (by omega) j))
      (KernelTowerCechHomology.shiftedPositiveIso (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
        T' (n - i) i (by simpa [hi'] using hn.le) (fun q hq j => hT' q (by omega) j))
      (TowerCechPositiveNaturality.Kernel.shiftedPositive (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
        a (n - i) i (by simpa [hi'] using hn.le)
        (fun q hq j => hT q (by omega) j) (fun q hq j => hT' q (by omega) j))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.CohomologyNaturality
