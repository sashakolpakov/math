import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjectionNaturality

/-! # Open Conormal Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalCoordinates

noncomputable section

/-! Conormal coordinates on an actual affine open subfamily use its
own global-section algebra and its actual affine coordinate isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (A : Over (Spec (.of k)))
    (Y : Over (Spec (.of k))) [IsAffine Y.left] (i : Y ⟶ A) [IsOpenImmersion i.left]

def affineOpenCoordinateIso : Y ≅ EtaleSplittingAt.EtaleSplitting.affineOver k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :=
  HilbertConstruction.Affine.OverChartPoints.affineOverIso k Y

def affineOpenCoordinateInclusion : EtaleSplittingAt.EtaleSplitting.affineOver k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) ⟶ A :=
  (affineOpenCoordinateIso k Y).inv ≫ i

instance affineOpenCoordinateInclusion_open : IsOpenImmersion (affineOpenCoordinateInclusion k A Y i).left := by
  have : IsIso (affineOpenCoordinateIso k Y).inv.left := (Over.forget _).map_isIso (affineOpenCoordinateIso k Y).inv
  have : IsOpenImmersion (affineOpenCoordinateIso k Y).inv.left := IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp _ _

variable [GrpObj A] [Smooth A.hom]

def affineOpenConormalEquiv :
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) ≃
      (Constructed.IdentityConormal.constructedIdentityConormal k A →ₗ[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :=
  ChartCoefficientConormal.affineChartCoefficientConormalEquiv k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y)
    A (affineOpenCoordinateInclusion k A Y i)

variable (Z : Over (Spec (.of k))) [IsAffine Z.left] (j : Z ⟶ A) [IsOpenImmersion j.left]
    (f : Z ⟶ Y)

omit [GrpObj A] [Smooth A.hom] [IsOpenImmersion i.left] [IsOpenImmersion j.left] in
theorem affineOpenCoordinateInclusion_natural (hf : f ≫ i = j) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Z) (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f) ≫
      affineOpenCoordinateInclusion k A Y i = affineOpenCoordinateInclusion k A Z j := by
  have he : AlgebraAutomorphismNaturality.affineOverAlgHom k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Z)
      (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f) ≫ (affineOpenCoordinateIso k Y).inv = (affineOpenCoordinateIso k Z).inv ≫ f := by
    apply Over.OverMorphism.ext
    exact HilbertConstruction.Affine.TensorProjectionNaturality.affineOverMap_spec_inv f
  change _ ≫ ((affineOpenCoordinateIso k Y).inv ≫ i) = (affineOpenCoordinateIso k Z).inv ≫ j
  rw [← Category.assoc, he, Category.assoc, hf]

theorem affineOpenConormalEquiv_natural (hf : f ≫ i = j)
    (he : (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f).toRingHom.Etale)
    (d : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y))
    (z : Constructed.IdentityConormal.constructedIdentityConormal k A) :
    affineOpenConormalEquiv k A Z j (EtaleHomDerivation.etaleAlgHomDerivationLinear (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f) he d) z =
      HilbertConstruction.Affine.OverMorphisms.affineOverMap k f (affineOpenConormalEquiv k A Y i d z) :=
  ChartConormalRestriction.affineChartCoefficientConormalEquiv_restriction k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Z)
    (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f) he A (affineOpenCoordinateInclusion k A Y i) (affineOpenCoordinateInclusion k A Z j)
    (affineOpenCoordinateInclusion_natural k A Y i Z j f hf) d z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalCoordinates
