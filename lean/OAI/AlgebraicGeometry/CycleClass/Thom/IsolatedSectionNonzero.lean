import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSupportAvoidance
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing

/-! # Isolated Section Nonzero -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionNonzero.Constructions

noncomputable section

/-! A single equation in an isolated cut at a higher-codimension
generic point is nonzero on the actual original parent support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSupportAvoidance.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem parentFunction_ne_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p d : ℕ)
    (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (Z : Geometric.DimensionCycles.DimensionCycleSupport V d) (hp : p < d)
    (hxD : IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier))
    (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B)
    [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hi : PrimeSpectrum.zeroLocus
      (Ideal.ofList [V.carrier.presheaf.germ B (IntersectionGeometry.supportPoint Z.val) hxB (B.topIso.hom r)] :
        Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))) ∩
      Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
        (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val (IntersectionGeometry.supportPoint Z.val) hxD) ⊆
          {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))}) :
    Affine.SectionFunction.Constructions.parentSectionFunction D B r ≠ 0 := by
  have hnot := IsolatedSupportAvoidance.Constructions.ideal_not_le_supportKernel V p d D Z hp hxD
    [V.carrier.presheaf.germ B (IntersectionGeometry.supportPoint Z.val) hxB (B.topIso.hom r)] hi
  apply (Section.StalkNonvanishing.Constructions.parentFunction_ne_zero_iff D B r (IntersectionGeometry.supportPoint Z.val) hxD hxB).mpr
  intro hz
  apply hnot
  rw [Ideal.ofList_singleton]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hz)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionNonzero.Constructions
