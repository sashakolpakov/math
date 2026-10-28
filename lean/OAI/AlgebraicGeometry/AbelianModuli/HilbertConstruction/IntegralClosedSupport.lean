import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Integral Closed Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralClosedSupport

noncomputable section

/-! The actual vanishing-ideal subscheme of an irreducible closed set
is integral. Its affine charts are the actual reduced quotient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem vanishingIdeal_subscheme_reduced
    {X : Scheme.{u}} (Z : Closeds X) : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred (U : X.affineOpens) : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have (U : I.subschemeCover.openCover.I₀) : IsReduced (I.subschemeCover.openCover.X U) := by
    let V : X.affineOpens := U
    have := hred V
    change IsReduced (Spec (.of (Γ(X, V.1) ⧸ I.ideal V)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem vanishingIdeal_subscheme_integral
    {X : Scheme.{u}} (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsReduced I.subscheme := vanishingIdeal_subscheme_reduced Z
  have hr : Set.range I.subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hi : IsIrreducible (Set.range I.subschemeι) := hr.symm ▸ hZ
  have : IrreducibleSpace (Set.range I.subschemeι) := Subtype.irreducibleSpace hi
  let e := (IsClosedImmersion.isClosedEmbedding I.subschemeι).isEmbedding.toHomeomorph
  have : IrreducibleSpace I.subscheme := e.irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralClosedSupport
