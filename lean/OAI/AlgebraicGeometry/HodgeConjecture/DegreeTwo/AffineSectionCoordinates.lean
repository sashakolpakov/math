import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover

/-! # Affine Section Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions

noncomputable section

section

/-!
# DegreeTwo: affine characters evaluate the actual scheme sections

The canonical spectrum-of-sections isomorphism identifies the affine
character space with the actual analytic open, and preserves section values.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (U : X.carrier.Opens) (hU : IsAffineOpen U)

/-- The canonical affine-open spectrum isomorphism, with the scalar
structure induced by the original complex structure morphism. -/
def affineSectionOverIso : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openOver U ≅
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) :=
  Over.isoMk hU.isoSpec (by
    change hU.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap X.structureMap U)) =
        U.ι ≫ X.structureMap
    rw [Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec X.structureMap U hU,
      ← Category.assoc, hU.isoSpec_hom_fromSpec])

/-- Characters of the actual section algebra are exactly points of the
corresponding actual analytic open. -/
def affineSectionPointHomeomorph :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) ≃ₜ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U :=
  ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)).trans
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (affineSectionOverIso X U hU)).symm).trans
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U)

theorem affineSectionPointHomeomorph_val
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)) :
    (affineSectionPointHomeomorph X U hU y).val =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X.toOver U hU) y := by
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) y ≫
      (affineSectionOverIso X U hU).inv) ≫ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openInclusion X U =
    ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) y ≫
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X.toOver U hU
  rw [Category.assoc]
  congr 1

/-- Native evaluation of an actual scheme section is ordinary character
evaluation under the canonical affine chart. -/
theorem affineSectionPointHomeomorph_evaluation
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U))
    (a : Γ(X.carrier, U)) :
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U a (affineSectionPointHomeomorph X U hU y) = y a := by
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation
      ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U).symm ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (affineSectionOverIso X U hU).inv
          (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U) y))))
      (U.topIso.inv a) = y a
  rw [Homeomorph.symm_apply_apply, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_affine]
  change y ((Scheme.ΓSpecIso Γ(X.carrier, U)).hom
    (hU.isoSpec.inv.appTop (U.topIso.inv a))) = y a
  rw [hU.isoSpec_inv_appTop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

end

/-!
# DegreeTwo: affine section kernels describe the actual prime-divisor support

Specialization of genuine scheme points is reflected by the canonical
affine-open embedding. Thus prime containment in a character kernel is
exactly membership in the corresponding scheme-point closure.
-/

open scoped _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (U : X.carrier.Opens) (hU : IsAffineOpen U)

theorem affineSectionPoint_specializes_iff (z : U)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)) :
    z.val ⤳ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (affineSectionPointHomeomorph X U hU y).val ↔
      (hU.primeIdealOf z).asIdeal ≤ RingHom.ker y.toRingHom := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
  rw [affineSectionPointHomeomorph_val, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap]
  change z.val ⤳ hU.fromSpec (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum y) ↔ _
  rw [← hU.fromSpec_primeIdealOf z]
  erw [hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes (hU.primeIdealOf z)
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum y)).symm

theorem affineSectionPoint_mem_pointClosure_iff (z : U)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X.toOver U)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (affineSectionPointHomeomorph X U hU y).val ∈
        closure ({z.val} : Set X.carrier) ↔
      (hU.primeIdealOf z).asIdeal ≤ RingHom.ker y.toRingHom := by
  exact (specializes_iff_mem_closure (x := z.val)
    (y := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (affineSectionPointHomeomorph X U hU y).val)).symm.trans
      (affineSectionPoint_specializes_iff X U hU z y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates.Constructions
