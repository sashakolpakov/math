import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineIsomorphismDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverPullbackProperties
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedSquareComparisonIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComparisonPullback

/-! # Ambient Square Pullback Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientSquarePullbackDescent

noncomputable section

/-! Finitely many ambient overlap squares become Cartesian over one finite coefficient extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem exists_common_ambient_square_pullbacks
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {I : Type v} [Finite I] (A B X Y : I → Over (Spec (.of C)))
    [∀ i, IsAffine (A i).left] [∀ i, IsAffine (B i).left]
    [∀ i, IsAffine (X i).left] [∀ i, IsAffine (Y i).left]
    [∀ i, Smooth (A i).hom] [∀ i, Smooth (B i).hom]
    (f : ∀ i, A i ⟶ B i) (a : ∀ i, A i ⟶ X i) (b : ∀ i, B i ⟶ Y i) (g : ∀ i, X i ⟶ Y i)
    [∀ i, IsOpenImmersion (g i).left] (h : ∀ i, f i ≫ b i = a i ≫ g i)
    [∀ i, IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map (a i))]
    [∀ i, IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map (b i))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, IsPullback
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map (f i))
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map (a i))
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map (b i))
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map (g i)) := by
  let P (i : I) := pullback (b i) (g i)
  let c (i : I) : A i ⟶ P i := pullback.lift (f i) (a i) (h i)
  have (i : I) : IsAffine (P i).left := Affine.OverPullbackProperties.affineOverPullback_affine (b i) (g i)
  have (i : I) : Smooth (P i).hom := Affine.OverPullbackProperties.affineOverPullback_smooth (b i) (g i)
  have (i : I) : IsIso ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map (c i)) :=
    MappedSquareComparisonIso.isIso_mapped_pullbackLift_of_vert_isIso _ (f i) (a i) (b i) (g i) (h i)
  obtain ⟨D, hED, hD, hd⟩ := HilbertConstruction.Smooth.AffineIsomorphismDescent.exists_common_smooth_affine_isomorphisms A P c E hE
  refine ⟨D, hED, hD, ?_⟩
  intro i
  have : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map (c i)) := hd i
  exact MappedComparisonPullback.isPullback_of_mapped_comparison_isIso
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D))))
    (pullback.fst (b i) (g i)) (pullback.snd (b i) (g i)) (b i) (g i)
    (IsPullback.of_hasPullback (b i) (g i)) (c i) (f i) (a i)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientSquarePullbackDescent
