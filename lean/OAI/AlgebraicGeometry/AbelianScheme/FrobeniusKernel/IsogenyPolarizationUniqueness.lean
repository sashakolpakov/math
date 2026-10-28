import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardKernelFiniteness

/-! # Isogeny Polarization Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness.Construction

noncomputable section

/-!
The canonical Picard dual of every geometric isogeny is finite.
Consequently its pullback identity determines the entire polarization.
Finiteness is derived from actual line-bundle kernel characters and
global descent, and is not an extra quotient hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem isogeny_dualMap_finite : IsFinite (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p.hom DA DB).left := by
  let f := PicardPullback.Construction.IntrinsicPicardPullback.dualMap p.hom DA DB
  have : IsMonHom f := PicardGroupMap.Construction.IntrinsicPicardPullback.dualMap_isMonHom p.hom DA DB
  have he : f = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB p.hom :=
    Polarization.Construction.NativePicardPullback.dualMap_eq_e57 p.hom DA DB
  have hpoints : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) := by
    rw [he]
    exact CartierDuality.PicardKernelFiniteness.Construction.KernelCharacters.finite_geometric_dualKernel DA DB p.hom
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)
  exact Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel f

/-- Uniqueness under a native isogeny uses only the actual two
polarizations and their pullback equations. -/
theorem isogeny_polarization_eq_of_pullback_eq {δ : Fin h → ℕ}
    (pol₁ pol₂ : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ)
    (h : PolarizationComparison.Construction.polarizationPullbackHom p.hom DA DB pol₁ = PolarizationComparison.Construction.polarizationPullbackHom p.hom DA DB pol₂) :
    pol₁ = pol₂ := by
  have : IsFinite (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p.hom DA DB).left := isogeny_dualMap_finite p DA DB
  exact PolarizationComparison.Construction.polarization_eq_of_pullback_eq p DA DB pol₁ pol₂ h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness.Construction
