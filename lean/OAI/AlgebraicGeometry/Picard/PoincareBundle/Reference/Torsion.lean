import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Torsion

noncomputable section

/-! The original finite polarization isogeny supplies all positive-torsion cover and kernel geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

universe u

variable {k : Type u} [Field k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)

include ell hn

/-- Positive multiplication is a genuine finite flat cover, with affine scheme-theoretic kernel, in every characteristic. -/
theorem cover :
    IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left ∧
    Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left ∧
    Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left ∧
    LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left ∧
    IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left := by
  have : IsMonHom (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom) := ell.preservesGroup
  have : IsFinite (show A.scheme ⟶ (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian from ell.hom).left := ell.finite
  have h := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.scheme (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) ell.hom n hn
  have : IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.1
  have : IsFinite (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).hom :=
    Kernel.Scheme.kernel_isFinite ((𝟙 A.scheme) ^ n)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
    isAffine_of_isAffineHom (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).hom⟩

/-- The native equalizer kernel used by Cartier duality is finite locally free, without a prime-invertibility hypothesis. -/
theorem native_kernel :
    IsFinite (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)).hom ∧
    Flat (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)).hom ∧
    LocallyOfFinitePresentation (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)).hom := by
  have : IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := (cover D ell n hn).1
  exact AbelianScheme.CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.scheme) n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Torsion
