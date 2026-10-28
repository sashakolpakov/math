import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts

/-! # Etale Subchart Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates

noncomputable section

/-! Every affine subchart of the actual finite coordinate cover inherits its etale polynomial coordinates over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  (I : X.left.affineOpens) (i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)
  (hi : I.val ≤ ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i)

abbrev sourceRing : Type u := Γ(X.left, I.val)

local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.sourceRing R X I
local notation "σ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
local instance sourceAlgebra : Algebra R A := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X I.val

@[instance_reducible] def polynomialAlgebra : Algebra (MvPolynomial σ R) A :=
  @NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.polynomialAlgebra R inferInstance X I.val I.property
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing R X i) inferInstance
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap R X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open R X i) hi
    σ (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra R X i)

theorem etale : letI := polynomialAlgebra R X I i hi
    Algebra.Etale (MvPolynomial σ R) A :=
  @NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.etale R inferInstance X I.val I.property
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing R X i) inferInstance
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap R X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open R X i) hi
    σ (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra R X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateEtale R X i)

theorem tower : letI := polynomialAlgebra R X I i hi
    IsScalarTower R (MvPolynomial σ R) A :=
  @NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.tower R inferInstance X I.val I.property
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing R X i) inferInstance
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap R X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open R X i) hi
    σ (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra R X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateAlgebra R X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateTower R X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_over R X i)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates
