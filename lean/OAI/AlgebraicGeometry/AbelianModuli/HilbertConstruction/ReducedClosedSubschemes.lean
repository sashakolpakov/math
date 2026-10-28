import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Reduced Closed Subschemes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedClosedSubschemes

noncomputable section

/-! Reduced induced closed subschemes, constructed from their vanishing ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (X : Scheme.{u}) (Z : TopologicalSpace.Closeds X)

def reducedClosedSubscheme : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

def reducedClosedInclusion : reducedClosedSubscheme X Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

instance reducedClosedInclusion_isClosedImmersion : IsClosedImmersion (reducedClosedInclusion X Z) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

theorem reducedClosedInclusion_range : Set.range (reducedClosedInclusion X Z) = Z := by
  exact (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

instance reducedClosedSubscheme_isReduced : IsReduced (reducedClosedSubscheme X Z) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    change X.affineOpens at U
    change IsReduced (Spec (.of (Γ(X, U.1) ⧸ I.ideal U)))
    apply (affine_isReduced_iff _).mpr
    change _root_.IsReduced (Γ(X, U.1) ⧸ PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' Z))
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedClosedSubschemes
