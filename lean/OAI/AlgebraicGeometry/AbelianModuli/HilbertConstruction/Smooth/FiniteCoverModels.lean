import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothSchemeModels

/-! # Finite Cover Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiniteCoverModels

noncomputable section

/-! A finite affine cover of a smooth quasi-compact scheme has smooth models over one noetherian ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

abbrev finiteSmoothAffineChart (i : X.left.affineCover.finiteSubcover.I₀) : Over (Spec (.of R)) :=
  Over.mk (X.left.affineCover.finiteSubcover.f i ≫ X.hom)

instance finiteSmoothAffineChart_affine (i : X.left.affineCover.finiteSubcover.I₀) :
    IsAffine (finiteSmoothAffineChart X i).left := by
  change IsAffine (X.left.affineCover.finiteSubcover.X i)
  change IsAffine (Spec _)
  infer_instance

instance finiteSmoothAffineChart_smooth [Smooth X.hom] (i : X.left.affineCover.finiteSubcover.I₀) :
    Smooth (finiteSmoothAffineChart X i).hom :=
  inferInstanceAs (Smooth (X.left.affineCover.finiteSubcover.f i ≫ X.hom))

theorem exists_smooth_finite_cover_models [Smooth X.hom]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ D : Subalgebra ℤ R, C ≤ D ∧ Algebra.FiniteType ℤ D ∧ IsNoetherianRing D ∧
      ∃ M : ∀ i, AffineModels.SmoothAffineModel R (Affine.OverChartPoints.affineOverAlgebra R (finiteSmoothAffineChart X i)),
        (∀ i, (M i).coefficients = D) ∧
        ∀ i, ∃ q : (finiteSmoothAffineChart X i).left ⟶ Spec (.of (M i).algebra),
          IsPullback q (finiteSmoothAffineChart X i).hom (M i).structureMap
            (Spec.map (CommRingCat.ofHom (M i).coefficients.val.toRingHom)) :=
  Common.SmoothSchemeModels.exists_common_smoothAffineSchemeModels R (finiteSmoothAffineChart X) C

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiniteCoverModels
