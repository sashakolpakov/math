import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TensorLattice

/-! # Complex Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexBasis

noncomputable section

/-! Tate bases for HilbertConstruction's actual projective complex abelian schemes. The
rank is twice the stated relative dimension, through the native adapter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (q : ℕ) [Fact q.Prime]

local instance : IsIntegral A.scheme.left := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A

theorem nativeTateRank_eq_dimension : IntrinsicBasis.nativeTateRank (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) = 2 * g := by
  change 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom = 2 * g
  rw [AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A]

def complexTateBasis : Module.Basis (Fin (2 * g)) ℤ_[q]
    (Add.schemeTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) :=
  ((IntrinsicBasis.nativeTateBasis (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) q).map
    (TateProducts.Tate.mapEquiv q (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativePointEquiv A P).toAdditive)).reindex
      (finCongr (nativeTateRank_eq_dimension A P))

def complexRationalTateBasis : Module.Basis (Fin (2 * g)) ℚ_[q]
    (Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) :=
  (complexTateBasis A P q).baseChange ℚ_[q]

include P in
theorem complexTate_finrank :
    Module.finrank ℤ_[q] (Add.schemeTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) = 2 * g := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (complexTateBasis A P q)

include P in
theorem complexRationalTate_finrank :
    Module.finrank ℚ_[q] (Rational.rationalTateModule A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) = 2 * g := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (complexRationalTateBasis A P q)

include P in
theorem complexIntegralTateImage_isLattice :
    Submodule.IsLattice ℚ_[q] (Rational.integralTateImage A.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) :=
  TensorLattice.tensorIntegralImage_isLattice (complexTateBasis A P q)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexBasis
