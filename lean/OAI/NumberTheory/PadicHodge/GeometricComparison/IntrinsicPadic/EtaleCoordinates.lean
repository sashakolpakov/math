import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.EtaleCoordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame

/-! # Etale Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleCoordinates

/-! The actual p-adic section rings on the integral finite coordinate cover
carry étale polynomial coordinates over the native Witt base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)

local notation "W" => WittVector p (ZMod p)
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "σ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X i

local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance wittAlgebra : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
local instance padicPolynomialAlgebra : Algebra (MvPolynomial σ ℤ_[p]) A :=
  Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.polynomialAlgebra ℤ_[p] X i
local instance padicTower : IsScalarTower ℤ_[p] (MvPolynomial σ ℤ_[p]) A :=
  Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.tower ℤ_[p] X i
local instance padicEtale : Algebra.Etale (MvPolynomial σ ℤ_[p]) A :=
  Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.etale ℤ_[p] X i

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ W) A :=
  EtaleCoordinate.EtaleCoordinateBaseEquiv.polynomialAlgebra W ℤ_[p] A σ (WittVector.equiv p)

theorem tower : letI := polynomialAlgebra p X i
    IsScalarTower W (MvPolynomial σ W) A :=
  EtaleCoordinate.EtaleCoordinateBaseEquiv.scalarTower W ℤ_[p] A σ (WittVector.equiv p)

theorem etale : letI := polynomialAlgebra p X i
    Algebra.Etale (MvPolynomial σ W) A :=
  EtaleCoordinate.EtaleCoordinateBaseEquiv.etale W ℤ_[p] A σ (WittVector.equiv p)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates

/-! Every affine subchart of a member of the actual integral coordinate
cover inherits its finite étale coordinates over the native Witt base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val
local notation "σ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X i
local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.val
local instance wittAlgebra : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A

@[instance_reducible]
def padicPolynomialAlgebra : Algebra (MvPolynomial σ ℤ_[p]) A :=
  @IntegralComparison.AffineOpen.EtaleCoordinates.polynomialAlgebra ℤ_[p] inferInstance X I.val I.property
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateRing ℤ_[p] X i) inferInstance
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap ℤ_[p] X i) (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_open ℤ_[p] X i) hi
    σ (Integral.EtaleAffineCover.IntegralEtaleAffineCover.polynomialAlgebra ℤ_[p] X i)

theorem padicEtale : letI := padicPolynomialAlgebra p X I i hi
    Algebra.Etale (MvPolynomial σ ℤ_[p]) A :=
  @IntegralComparison.AffineOpen.EtaleCoordinates.etale ℤ_[p] inferInstance X I.val I.property
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateRing ℤ_[p] X i) inferInstance
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap ℤ_[p] X i) (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_open ℤ_[p] X i) hi
    σ (Integral.EtaleAffineCover.IntegralEtaleAffineCover.polynomialAlgebra ℤ_[p] X i)
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateEtale ℤ_[p] X i)

theorem padicTower : letI := padicPolynomialAlgebra p X I i hi
    IsScalarTower ℤ_[p] (MvPolynomial σ ℤ_[p]) A :=
  @IntegralComparison.AffineOpen.EtaleCoordinates.tower ℤ_[p] inferInstance X I.val I.property
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateRing ℤ_[p] X i) inferInstance
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap ℤ_[p] X i) (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_open ℤ_[p] X i) hi
    σ (Integral.EtaleAffineCover.IntegralEtaleAffineCover.polynomialAlgebra ℤ_[p] X i)
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateAlgebra ℤ_[p] X i) (Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateTower ℤ_[p] X i)
    (Integral.EtaleAffineCover.IntegralEtaleAffineCover.chartMap_over ℤ_[p] X i)

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ W) A := by
  letI := padicPolynomialAlgebra p X I i hi
  exact EtaleCoordinate.EtaleCoordinateBaseEquiv.polynomialAlgebra W ℤ_[p] A σ (WittVector.equiv p)

theorem tower : letI := polynomialAlgebra p X I i hi
    IsScalarTower W (MvPolynomial σ W) A := by
  let := padicPolynomialAlgebra p X I i hi
  let : IsScalarTower ℤ_[p] (MvPolynomial σ ℤ_[p]) A := padicTower p X I i hi
  exact EtaleCoordinate.EtaleCoordinateBaseEquiv.scalarTower W ℤ_[p] A σ (WittVector.equiv p)

theorem etale : letI := polynomialAlgebra p X I i hi
    Algebra.Etale (MvPolynomial σ W) A := by
  let := padicPolynomialAlgebra p X I i hi
  let : Algebra.Etale (MvPolynomial σ ℤ_[p]) A := padicEtale p X I i hi
  exact EtaleCoordinate.EtaleCoordinateBaseEquiv.etale W ℤ_[p] A σ (WittVector.equiv p)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates

end

end OAI
