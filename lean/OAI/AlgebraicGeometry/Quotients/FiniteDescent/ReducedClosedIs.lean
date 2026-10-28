import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Reduced Closed Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedClosedIs.Construction.ReducedClosed

/-! The reduced scheme structure on an arbitrary closed subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isReduced {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have (U : I.subschemeCover.openCover.I₀) : IsReduced (I.subschemeCover.openCover.X U) := by
    have := hred U
    change IsReduced (Spec (.of (Γ(X, U.1) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

theorem range_ι {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

theorem irreducibleSpace {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  apply Subtype.irreducibleSpace
  simpa only [Scheme.IdealSheafData.coe_support_vanishingIdeal] using hZ

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedClosedIs.Construction.ReducedClosed
