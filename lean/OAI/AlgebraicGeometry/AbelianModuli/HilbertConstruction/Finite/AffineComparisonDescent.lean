import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ComparisonTensorIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Affine Comparison Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineComparisonDescent

noncomputable section

/-! Finitely many comparisons of smooth affine models with common recovery become isomorphisms together. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v

theorem exists_common_affine_comparison_tensor_bijective
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {I : Type v} [Finite I] (X Y : I → Over (Spec (.of C)))
    [∀ i, IsAffine (X i).left] [∀ i, IsAffine (Y i).left]
    [∀ i, Smooth (X i).hom] [∀ i, Smooth (Y i).hom]
    (f : ∀ i, X i ⟶ Y i) (P : I → Over (Spec (.of R)))
    (qX : ∀ i, (P i).left ⟶ (X i).left) (qY : ∀ i, (P i).left ⟶ (Y i).left)
    (hX : ∀ i, IsPullback (qX i) (P i).hom (X i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (hY : ∀ i, IsPullback (qY i) (P i).hom (Y i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (hq : ∀ i, qX i ≫ (f i).left = qY i)
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, Function.Bijective (Algebra.TensorProduct.map (AlgHom.id D D) (Affine.OverMorphisms.affineOverMap C (f i))) := by
  have (i : I) : Algebra.Smooth C (Affine.OverChartPoints.affineOverAlgebra C (X i)) := HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth C (X i)
  have (i : I) : Algebra.Smooth C (Affine.OverChartPoints.affineOverAlgebra C (Y i)) := HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth C (Y i)
  have hb (i : I) : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id R R) (Affine.OverMorphisms.affineOverMap C (f i))) := by
    exact isIso_SpecMap_iff.mp
      (Affine.ComparisonTensorIso.affineOverMap_tensor_isIso_of_common_recovery (f i) (P i).hom
        (qX i) (qY i) (hX i) (hY i) (hq i))
  exact NaturalTensorMapDescent.exists_common_natural_tensorMap_bijective
    (fun i => ↥(Affine.OverChartPoints.affineOverAlgebra C (Y i))) (fun i => ↥(Affine.OverChartPoints.affineOverAlgebra C (X i)))
    (fun i => Affine.OverMorphisms.affineOverMap C (f i)) hb E hE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineComparisonDescent
