import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIsoConverse
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

/-! # Affine Isomorphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineIsomorphismDescent

noncomputable section

/-! Finitely many morphisms of smooth affine schemes that become isomorphisms do so over finite coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v

theorem exists_common_smooth_affine_isomorphisms
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {I : Type v} [Finite I] (X Y : I → Over (Spec (.of C)))
    [∀ i, IsAffine (X i).left] [∀ i, IsAffine (Y i).left]
    [∀ i, Smooth (X i).hom] [∀ i, Smooth (Y i).hom]
    (f : ∀ i, X i ⟶ Y i)
    [∀ i, IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map (f i))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map (f i)) := by
  have (i : I) : Algebra.Smooth C (Affine.OverChartPoints.affineOverAlgebra C (X i)) := AffineSchemeModels.affineOverAlgebra_smooth C (X i)
  have (i : I) : Algebra.Smooth C (Affine.OverChartPoints.affineOverAlgebra C (Y i)) := AffineSchemeModels.affineOverAlgebra_smooth C (Y i)
  have hf (i : I) : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id R R) (Affine.OverMorphisms.affineOverMap C (f i))) :=
    Affine.PullbackIsoConverse.affine_tensor_bijective_of_pullback_isIso (R := R) (f i)
  obtain ⟨D, hED, hD, hd⟩ := NaturalTensorMapDescent.exists_common_natural_tensorMap_bijective
    (fun i => ↥(Affine.OverChartPoints.affineOverAlgebra C (Y i))) (fun i => ↥(Affine.OverChartPoints.affineOverAlgebra C (X i)))
    (fun i => Affine.OverMorphisms.affineOverMap C (f i)) hf E hE
  exact ⟨D, hED, hD, fun i => Affine.PullbackIso.isIso_affine_pullback_of_tensor_bijective (f i) (hd i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineIsomorphismDescent
