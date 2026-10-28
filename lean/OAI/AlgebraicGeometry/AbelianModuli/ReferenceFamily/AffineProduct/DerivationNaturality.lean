import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.CoordinateNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.TransitionDerivation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCoefficientNaturality

/-! # Derivation Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationNaturality

noncomputable section

/-! A commuting square of actual affine product automorphisms induces
the corresponding restriction square of derivations on their fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] {X Y : Over (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]

local instance affineProductDerivationNaturality_sourceCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

local instance affineProductDerivationNaturality_targetCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)

theorem affineProductAutomorphismAlgebra_natural (f : X ⟶ Y)
    (eX : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (eY : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj Y ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj Y)
    (h : eX.hom ≫ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f =
      (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f ≫ eY.hom) :
    (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f)).comp
        (Coordinates.affineProductAutomorphismAlgebra k Y eY).toAlgHom =
      (Coordinates.affineProductAutomorphismAlgebra k X eX).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f)) := by
  let M := Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f)
  have hc := IsoNaturalitySquares.conjugateIso_natural (Coordinates.affineProductCoordinates k X) (Coordinates.affineProductCoordinates k Y)
    ((Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f)
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k) (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)
      (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) M)
    (CoordinateNaturality.affineProductCoordinates_natural k f) eX eY h
  have hs := congrArg Over.Hom.left hc
  change (Coordinates.affineProductCoordinateAutomorphism k X eX).hom.left ≫ Spec.map (CommRingCat.ofHom M.toRingHom) =
    Spec.map (CommRingCat.ofHom M.toRingHom) ≫ (Coordinates.affineProductCoordinateAutomorphism k Y eY).hom.left at hs
  have hx := Coordinates.affineProductAutomorphismAlgebra_spec k X eX
  have hy := Coordinates.affineProductAutomorphismAlgebra_spec k Y eY
  rw [← hx, ← hy, ← Spec.map_comp, ← Spec.map_comp] at hs
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs.symm)
  exact AlgHom.ext (fun a => RingHom.congr_fun hr a)

theorem affineProductTransitionDerivation_natural (f : X ⟶ Y)
    (eX : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (eY : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj Y ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj Y)
    (heX : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map eX.hom = 𝟙 _)
    (heY : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map eY.hom = 𝟙 _)
    (h : eX.hom ≫ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f =
      (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).map f ≫ eY.hom)
    (a : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :
    HilbertConstruction.Affine.OverMorphisms.affineOverMap k f (TransitionDerivation.affineProductTransitionDerivation k Y eY heY a) =
      TransitionDerivation.affineProductTransitionDerivation k X eX heX (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f a) :=
  Dual.TensorCoefficientNaturality.dualTensorTransitionDerivation_natural (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f)
    (Coordinates.affineProductAutomorphismAlgebra k Y eY) (Coordinates.affineProductAutomorphismAlgebra k X eX)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k Y eY heY)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X eX heX)
    (affineProductAutomorphismAlgebra_natural k f eX eY h) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationNaturality
