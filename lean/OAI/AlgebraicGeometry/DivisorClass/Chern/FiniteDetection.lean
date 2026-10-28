import OAI.AlgebraicGeometry.DivisorClass.Chern.CodimensionOneDetection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Support

/-! # Finite Detection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteDetection

noncomputable section

/-!
# ChernClass: only finitely many divisor neighborhoods are needed for detection

Codimension-one points outside the reference open form the actual finite
set already proved algebraically. Restriction to neighborhoods of just those
points detects the whole relative class; the reference-open restriction is
zero by the actual support condition.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
local notation "O" => OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X L.rationalReferenceOpen

/-- The actual codimension-one points outside the chosen reference open. -/
abbrev _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.ReferenceDivisorPoint :=
  {z : X.carrier // Order.coheight z = 1 ∧ z ∉ L.rationalReferenceOpen}

instance _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.referenceDivisorPoint_finite : Finite L.ReferenceDivisorPoint := by
  let : Nonempty L.rationalReferenceOpen := ⟨⟨genericPoint X.carrier, L.mem_trivializingOpen _⟩⟩
  exact (Support.Construction.finite_codimension_one_complement X.carrier L.rationalReferenceOpen).to_subtype

/-- Every original relative class restricts to zero on the reference open. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeClass_reference_restriction_zero
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T) O 2 a = 0 := by
  apply (ModuleCat.mono_iff_injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of ℚ ℚ) T O O 2)).mp inferInstance
  apply CycleClass.Geometric.SupportedGerms.Cycles.supportedCohomologySection_ext_on_support (ModuleCat.of ℚ ℚ) T O O 2
  intro x hx hnot
  exact (hnot hx).elim

/-- Actual relative classes are determined by finitely many algebraic
neighborhood restrictions, one at each reference divisor point. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.relativeClass_eq_of_finite_divisor_restrictions
    (U : L.ReferenceDivisorPoint → X.carrier.Opens) (hU : ∀ z, z.val ∈ U z)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2)
    (hab : ∀ z, CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
      (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
        (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 b) : a = b := by
  classical
  let V (z : {z : X.carrier // Order.coheight z = 1}) : X.carrier.Opens :=
    if hz : z.val ∈ L.rationalReferenceOpen then L.rationalReferenceOpen
    else U ⟨z.val, z.property, hz⟩
  have hV (z : {z : X.carrier // Order.coheight z = 1}) : z.val ∈ V z := by
    dsimp only [V]
    split_ifs with hz
    · exact hz
    · exact hU ⟨z.val, z.property, hz⟩
  apply L.relativeClass_eq_of_codimensionOne_restrictions V hV a b
  intro z
  by_cases hz : z.val ∈ L.rationalReferenceOpen
  · have he : V z = L.rationalReferenceOpen := dite_eq_left hz
    rw [he, L.relativeClass_reference_restriction_zero a, L.relativeClass_reference_restriction_zero b]
  · have he : V z = U ⟨z.val, z.property, hz⟩ := dite_eq_right hz
    rw [he]
    exact hab ⟨z.val, z.property, hz⟩

/-- The finite family of actual restrictions is injective. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.finite_divisor_restriction_injective
    (U : L.ReferenceDivisorPoint → X.carrier.Opens) (hU : ∀ z, z.val ∈ U z) :
    Function.Injective (fun a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T (O : Set T) 2 =>
      fun z : L.ReferenceDivisorPoint =>
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T (O : Set T)
          (Line.Bundles.AlgebraicLineBundle.analyticOpen X (U z)) 2 a) := by
  intro a b hab
  exact L.relativeClass_eq_of_finite_divisor_restrictions U hU a b (congrFun hab)

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteDetection
