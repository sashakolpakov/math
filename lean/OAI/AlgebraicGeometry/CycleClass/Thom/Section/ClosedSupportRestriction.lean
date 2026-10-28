import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange

/-! # Closed Support Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupportRestriction.Constructions

noncomputable section

/-! The global section supports for two nested bases agree on every
analytic open lying in the smaller base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B C : V.carrier.Opens) (hCB : C ≤ B) (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))

omit D in
theorem basicOpen_sectionRestriction :
    V.carrier.basicOpen (C.topIso.hom ((V.carrier.homOfLE hCB).appTop s)) =
      C ⊓ V.carrier.basicOpen (B.topIso.hom s) := by
  rw [BaseRestriction.Constructions.topIso_sectionRestriction B C hCB s, Scheme.basicOpen_res]

 theorem sectionClosedSupport_restrict (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C))) :
    {x : U | V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D C ((V.carrier.homOfLE hCB).appTop s)} =
      {x : U | V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D B s} := by
  ext x
  have hxC : V.analyticUnderlying x.val ∈ C :=
    (Set.ext_iff.mp (NormalizationAffine.OpenRange.Constructions.baseInclusion_analytic_range C) x.val).mp (hU x.property)
  change (V.analyticUnderlying x.val ∈ (D.val : Set V.carrier) ∧
      V.analyticUnderlying x.val ∉ V.carrier.basicOpen (C.topIso.hom ((V.carrier.homOfLE hCB).appTop s))) ↔
    (V.analyticUnderlying x.val ∈ (D.val : Set V.carrier) ∧
      V.analyticUnderlying x.val ∉ V.carrier.basicOpen (B.topIso.hom s))
  rw [basicOpen_sectionRestriction B C hCB s]
  change (_ ∧ ¬ (_ ∧ _)) ↔ _
  constructor
  · intro h
    exact ⟨h.1, fun hz => h.2 ⟨hxC, hz⟩⟩
  · intro h
    exact ⟨h.1, fun hz => h.2 hz.2⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupportRestriction.Constructions
