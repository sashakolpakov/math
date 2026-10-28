import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualChartCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient

/-! # Dual Open Chart Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualOpenChartCoefficients.Construction

noncomputable section

/-! The native affine coefficient chart on an actual dual-family open
computes the original Picard Cech coefficients. The chart and its open
factorization are constructed; no coefficient compatibility is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (hU : IsAffineOpen U)

/-- The original coefficient scheme maps isomorphically to the given open
through the canonical presentation of its actual reduced open. -/
def nativeDualOpenCoefficientChart :
    Spec (.of (DualNumber Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤))) ⟶ U.toScheme := by
  letI : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  exact (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)
    (CommAlgCat.of ℂ Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤))
    (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv).left ≫ (AbelianModuli.ReferenceFamily.DualOpen.Product.dualOpenProductIso X U).hom

theorem nativeDualOpenCoefficientChart_inclusion :
    letI : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
    nativeDualOpenCoefficientChart X U hU ≫ U.ι =
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)
        (CommAlgCat.of ℂ Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤))
        (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U)).inv).left ≫ AbelianModuli.ReferenceFamily.DualOpen.Product.dualOpenProductMap X U := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  erw [nativeDualOpenCoefficientChart, Category.assoc, AbelianModuli.ReferenceFamily.DualOpen.Product.dualOpenProductIso_hom_ι]

/-- Both coefficients are those of the original open-section equivalence,
including the actual reduced-open global-section identification. -/
theorem nativeDualOpenCoefficientChart_coefficients (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (R := Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤))
      (S := Γ(X.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U))
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom.hom
      ((Scheme.ΓSpecIso (.of (DualNumber Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤)))).hom.hom
        ((nativeDualOpenCoefficientChart X U hU).appTop.hom (U.topIso.inv.hom s))) =
      AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s := by
  let : IsAffine (AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left := AbelianModuli.ReferenceFamily.Dual.ReductionOpens.dualAffineOpen_reduction X U hU
  rw [nativeDualOpenCoefficientChart, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [AbelianModuli.ReferenceFamily.CanonicalDualChartCoefficients.canonicalDualChart_sectionCoefficients]
  rfl

/-- In particular, the first-order coefficient is transported on the
original reduced open, rather than merely agreeing at closed points. -/
theorem nativeDualOpenCoefficientChart_firstCoefficient
    (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)) :
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom
      ((Scheme.ΓSpecIso (.of (DualNumber Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤)))).hom.hom
        ((nativeDualOpenCoefficientChart X U hU).appTop.hom (U.topIso.inv.hom s))).snd =
      (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU s).snd :=
  congrArg TrivSqZeroExt.snd (nativeDualOpenCoefficientChart_coefficients X U hU s)

theorem nativeDualOpenCoefficientChart_units (u : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, U)ˣ) :
    Units.map
      (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (R := Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤))
      (S := Γ(X.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U))
      ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).topIso.hom.hom).toMonoidHom
      (Units.map (Scheme.ΓSpecIso (.of (DualNumber Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X U).left, ⊤)))).hom.hom.toMonoidHom
        (Units.map (nativeDualOpenCoefficientChart X U hU).appTop.hom.toMonoidHom
          (Units.map U.topIso.inv.hom.toMonoidHom u))) =
      Units.map (AbelianModuli.ReferenceFamily.DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X U hU).toMonoidHom u :=
  Units.ext (nativeDualOpenCoefficientChart_coefficients X U hU u.val)

/-- The same constructed chart computes the literal coefficients on every
finite Cech intersection, with its original reduced-intersection transport. -/
theorem nativeDualCechChart_coefficients
    {I : Type} (V : I → (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    [IsAffineHom (pullback.diagonal (terminal.from (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (hV : ∀ i, IsAffineOpen (V i)) {n : ℕ} (a : Fin (n + 1) → I)
    (s : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)) :
    AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualReducedCechIntersection X V a)).toRingHom
      (AbelianModuli.ReferenceFamily.Dual.NumberCoefficients.dualNumberRingMap
        (R := Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)).left, ⊤))
        (S := Γ(X.left, (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a))
        ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a).topIso.hom.hom
        ((Scheme.ΓSpecIso (.of (DualNumber
          Γ((AbelianModuli.ReferenceFamily.DualOpen.Product.dualReducedOpenOver X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)).left, ⊤)))).hom.hom
          ((nativeDualOpenCoefficientChart X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)
            (AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualCechIntersection_affine X V hV a)).appTop.hom
              ((show (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens from AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a).topIso.inv.hom s)))) =
      AbelianModuli.ReferenceFamily.Dual.CechCoefficient.dualCechSectionCoefficientEquiv X V hV a s := by
  rw [nativeDualOpenCoefficientChart_coefficients]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DualOpenChartCoefficients.Construction
