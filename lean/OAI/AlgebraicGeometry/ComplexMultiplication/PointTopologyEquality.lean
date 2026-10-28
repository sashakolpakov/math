import OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologies
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology
import OAI.AlgebraicGeometry.ComplexPoint.Open
import OAI.AlgebraicGeometry.ComplexPoint.AffineSpace

/-! # Point Topology Equality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologyEquality

noncomputable section

/-! # Equality of the actual complex-point topologies

The affine-test topology of the older library and the regular-function topology
of the original framework are compared on their unchanged scheme-point carrier.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint
open scoped CommRingCat.HomTopology

variable (X : Over (Spec (.of ℂ))) (U : X.left.Opens) [IsAffine U.toScheme]

local instance CMPointTopologyEquality.localInstance1 : IsAffine (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U).left := inferInstanceAs (IsAffine U.toScheme)

local instance CMPointTopologyEquality.localInstance2 : Algebra ℂ Γ(U.toScheme, ⊤) :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineOverGammaAlgebra (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)

private def chartCharacters : ComplexPoint.Basic.Point.OverOpen (X := X) U →
    (Γ(U.toScheme, ⊤) →ₐ[ℂ] ℂ) :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) ∘ (ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm

private theorem chartCharacters_eval (s : Γ(U.toScheme, ⊤))
    (q : ComplexPoint.Basic.Point.OverOpen (X := X) U) :
    chartCharacters X U q s =
      ComplexPoint.Basic.Point.evaluate (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv s) q.val := by
  change Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) ((ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm q) s = _
  rw [Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_eval, ← ComplexPoint.Basic.ComplexSchemePoint.evaluate_top_eq_appTop]
  have hmap : ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U) ((ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm q) = q.val :=
    congrArg Subtype.val ((ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).apply_symm_apply q)
  exact (ComplexPoint.Basic.ComplexSchemePoint.evaluate_openEquiv X U s ((ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm q)).symm.trans
    (congrArg (ComplexPoint.Basic.Point.evaluate (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv s)) hmap)

private theorem chartCharacters_continuous :
    @Continuous (ComplexPoint.Basic.Point.OverOpen (X := X) U) (Γ(U.toScheme, ⊤) →ₐ[ℂ] ℂ)
      (ComplexPoint.Basic.Point.chartTopology U) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.instTopologicalSpace)
      (chartCharacters X U) := by
  let : TopologicalSpace (ComplexPoint.Basic.Point.OverOpen (X := X) U) := ComplexPoint.Basic.Point.chartTopology U
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff (chartCharacters X U)).mpr
  intro s
  let t := (U.ι.appIso ⊤).inv s
  let tU := X.left.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op t
  have hc : Continuous (fun q : ComplexPoint.Basic.Point.OverOpen (X := X) U => ComplexPoint.Basic.Point.evaluationHom U q tU) :=
    (CommRingCat.HomTopology.continuous_apply tU).comp
      (show Continuous (ComplexPoint.Basic.Point.evaluationHom U) from continuous_induced_dom)
  apply hc.congr
  intro q
  rw [chartCharacters_eval, ComplexPoint.Basic.ComplexSchemePoint.evaluate_eq (Scheme.Opens.ι_image_top U)]
  exact ComplexPoint.Basic.Point.evaluationHom_apply U q tU

private theorem chartToAffineTest_continuous :
    @Continuous (ComplexPoint.Basic.Point.OverOpen (X := X) U) (ComplexPoint.Basic.ComplexSchemePoint X)
      (ComplexPoint.Basic.Point.chartTopology U) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X)
      Subtype.val := by
  let : TopologicalSpace (ComplexPoint.Basic.Point.OverOpen (X := X) U) := ComplexPoint.Basic.Point.chartTopology U
  let : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint X) := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X
  let : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)) :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)
  have hc := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U)).comp
    ((ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)).continuous_invFun.comp
      (chartCharacters_continuous X U))
  apply hc.congr
  intro q
  change ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X U)
    ((Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)).symm
      (Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U) ((ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).symm q))) = q.val
  rw [Equiv.symm_apply_apply]
  exact congrArg Subtype.val ((ComplexPoint.Basic.ComplexSchemePoint.openEquiv X U).apply_symm_apply q)

omit [IsAffine U.toScheme] in
/-- The identity from the original analytic topology to the older affine-test topology is continuous. -/
theorem analyticToAffineTest_continuous :
    @Continuous (ComplexPoint.Basic.ComplexSchemePoint X) (ComplexPoint.Basic.ComplexSchemePoint X)
      ComplexPoint.Basic.Point.analyticTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X) id := by
  change @Continuous _ _
    (⨆ V : X.left.affineOpens,
      TopologicalSpace.coinduced (Subtype.val : ComplexPoint.Basic.Point.OverOpen (X := X) V.val → _)
        (ComplexPoint.Basic.Point.chartTopology V.val)) _ id
  simp only [continuous_iSup_dom, continuous_coinduced_dom, Function.comp_def, id_eq]
  intro V
  let : IsAffine V.val.toScheme := V.property
  exact chartToAffineTest_continuous X V.val

omit [IsAffine U.toScheme] in
/-- Both libraries use the same topology on their actual scheme-valued complex points. -/
theorem complexPointTopologies_eq :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X =
      (ComplexPoint.Basic.Point.analyticTopology : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  le_antisymm
    (continuous_id_iff_le.mp (PointTopologies.affineTestToAnalytic_continuous X))
    (continuous_id_iff_le.mp (analyticToAffineTest_continuous X))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologyEquality
