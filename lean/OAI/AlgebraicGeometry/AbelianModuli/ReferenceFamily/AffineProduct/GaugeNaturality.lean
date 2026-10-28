import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ChartGaugeCancellation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.CoordinateNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorGaugeNaturality

/-! # Gauge Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.GaugeNaturality

noncomputable section

/-! Actual scheme gauges commute with the original affine product
maps whenever their derivations commute with the actual coefficient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k : Type) [Field k] {X Y : Over (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]

local instance affineProductGaugeNaturality_sourceCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

local instance affineProductGaugeNaturality_targetCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)

theorem affineProductDerivationGauge_natural (f : X ⟶ Y)
    (dX : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X))
    (dY : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y))
    (h : ∀ a, HilbertConstruction.Affine.OverMorphisms.affineOverMap k f (dY a) = dX (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f a)) :
    (ChartGaugeCancellation.affineProductDerivationGauge k X dX).hom ≫ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f =
      (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f ≫ (ChartGaugeCancellation.affineProductDerivationGauge k Y dY).hom := by
  let q := HilbertConstruction.Affine.OverMorphisms.affineOverMap k f
  let m := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
    (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q)
  have hi := IsoNaturalitySquares.iso_inverse_square (Coordinates.affineProductCoordinates k X) (Coordinates.affineProductCoordinates k Y)
    ((Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f) m (CoordinateNaturality.affineProductCoordinates_natural k f)
  have hm := Affine.AlgebraAutomorphismNaturality.affineAlgIso_natural (DualNumber k)
    (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)
    (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q)
    (Dual.TensorDerivationGauges.dualTensorDerivationGauge dY) (Dual.TensorDerivationGauges.dualTensorDerivationGauge dX)
    (Dual.TensorGaugeNaturality.dualTensorDerivationGauge_natural q dY dX h)
  exact IsoNaturalitySquares.conjugateIso_natural (Coordinates.affineProductCoordinates k X).symm (Coordinates.affineProductCoordinates k Y).symm
    m ((Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f) hi
    (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (Dual.TensorDerivationGauges.dualTensorDerivationGauge dX))
    (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (Dual.TensorDerivationGauges.dualTensorDerivationGauge dY)) hm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.GaugeNaturality
