import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldAffineChartDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothEtaleCoordinates

/-! # Field Etale Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldEtaleCoordinates

noncomputable section

/-! Every point of a smooth g-dimensional scheme over a field has an actual affine chart with an etale polynomial-coordinate map in g variables, respecting the original ground-field coefficient map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem smoothField_exists_affine_etale_coordinates
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (g : ℕ) [SmoothOfRelativeDimension g p] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (ι : Type) (_ : Finite ι) (φ : MvPolynomial ι K →+* Γ(X, V)),
      Nat.card ι = g ∧ φ.Etale ∧
      φ.comp MvPolynomial.C =
        ((p.appTop ≫ X.presheaf.map V.leTop.op).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) := by
  obtain ⟨V, hV, hx, hstd⟩ := FieldAffineChartDimension.smoothField_exists_affine_chart_dimension p g x
  let c : K →+* Γ(X, V) :=
    (p.appTop ≫ X.presheaf.map V.leTop.op).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let : Algebra K Γ(X, V) := c.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g K Γ(X, V) := hstd
  obtain ⟨ι, hι, y, hcard, het⟩ := StandardSmoothEtaleCoordinates.exists_etale_polynomial_coordinates_of_standardSmooth K Γ(X, V) g
  let : Finite ι := hι
  let φ : MvPolynomial ι K →ₐ[K] Γ(X, V) := MvPolynomial.aeval y
  exact ⟨V, hV, hx, ι, hι, φ.toRingHom, hcard, het, φ.comp_algebraMap⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldEtaleCoordinates
