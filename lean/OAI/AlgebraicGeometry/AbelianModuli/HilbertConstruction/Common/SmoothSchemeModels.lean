import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAffineModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

/-! # Smooth Scheme Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothSchemeModels

noncomputable section

/-! Finitely many smooth affine schemes descend over one coefficient ring with actual pullback maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
variable (X : ι → Over (Spec (.of R))) [∀ i, IsAffine (X i).left] [∀ i, Smooth (X i).hom]

theorem exists_common_smoothAffineSchemeModels (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ D : Subalgebra ℤ R, C ≤ D ∧ Algebra.FiniteType ℤ D ∧ IsNoetherianRing D ∧
      ∃ M : ∀ i, HilbertConstruction.Smooth.AffineModels.SmoothAffineModel R (Affine.OverChartPoints.affineOverAlgebra R (X i)),
        (∀ i, (M i).coefficients = D) ∧
        ∀ i, ∃ q : (X i).left ⟶ Spec (.of (M i).algebra),
          IsPullback q (X i).hom (M i).structureMap
            (Spec.map (CommRingCat.ofHom (M i).coefficients.val.toRingHom)) := by
  have (i : ι) : Algebra.Smooth R (Affine.OverChartPoints.affineOverAlgebra R (X i)) := HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth R (X i)
  obtain ⟨D, hCD, hD, hn, M, hM⟩ :=
    SmoothAffineModels.exists_common_smoothAffineModels R (fun i => Affine.OverChartPoints.affineOverAlgebra R (X i)) C
  exact ⟨D, hCD, hD, hn, M, hM,
    fun i => ⟨HilbertConstruction.Smooth.AffineSchemeModels.affineSchemeModelMap R (X i) (M i), HilbertConstruction.Smooth.AffineSchemeModels.affineSchemeModel_isPullback R (X i) (M i)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothSchemeModels
