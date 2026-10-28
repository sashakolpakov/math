import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.KernelUnramified
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.DiagonalPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualDimensionEtaleSchemes

/-! # Isogeny Etale -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The finite-flat isogeny with the specified positive geometric polarization type is etale over the original arbitrary base. Its actual kernel is consequently finite etale. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.etale
    {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) : Etale p.hom.left := by
  have := hp.kernel_formallyUnramified hδ
  have := p.formallyUnramified_of_kernel
  have : SmoothOfRelativeDimension g (p.hom.left ≫ B.scheme.hom) := by
    rw [p.hom.w]
    infer_instance
  exact EqualDimensionEtaleSchemes.etale_of_smooth_equal_dimension p.hom.left B.scheme.hom g

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_etale
    {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) : Etale p.kernelScheme.hom := by
  have := hp.etale hδ
  exact inferInstanceAs (Etale (pullback.snd p.hom.left _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
