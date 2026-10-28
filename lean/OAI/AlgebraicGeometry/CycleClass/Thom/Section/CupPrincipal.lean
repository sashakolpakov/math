import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.SectionRestriction

/-! # Cup Principal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipal.Constructions

noncomputable section

/-! Supported cycle-section compatibility on an actual affine base
inside the smooth-normalization base, with all divisor comparison
boundaries removed from the hypotheses by actual supported purity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.SectionRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)
  [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] [IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

include hB in
theorem sectionCupClass_eq_principal : Cup.Constructions.Class.sectionCupClass D B s U hU = Principal.Constructions.Class.sectionPrincipalClass D B s hs U := by
  apply SectionRestriction.Constructions.retainedRestriction_injective D B s hs U
  let R := SectionRestriction.Constructions.retainedNeighborhood D B s hs U
  have hRU : R ≤ U := inf_le_left
  have hR : (R : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)) :=
    fun _ hx => hU (hRU hx)
  have he : Cup.Constructions.Class.sectionCupClass D B s R hR = Principal.Constructions.Class.sectionPrincipalClass D B s hs R :=
    CupPrincipalDetection.Constructions.sectionCupClass_eq_principal_on_retained_open D B hB s hs R hR
      (fun x hx => BoundaryRemoval.Constructions.retained_supportPoint_good D B s hs x.val hx x.property.2)
  exact (CupRestriction.Constructions.sectionCupClass_restrict D B s U R hRU hU hR).trans
    (he.trans (Principal.Constructions.Class.sectionPrincipalClass_restrict D B s hs U R hRU).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipal.Constructions
