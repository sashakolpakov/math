import OAI.RepresentationTheory.Theta.Geometric.Reference.PoincareDetection
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual
import OAI.RepresentationTheory.Theta.Geometric.Reference.PELFamily
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

/-! # PEL Compatibility -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference

noncomputable section

/-! Native Picard pullback and the original Chern pairing prove Rosati
compatibility. Thus the constructed reference family satisfies every
literal PEL condition, including the geometric Lie signature. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} (C : PolarizationConstruction.ReferencePolarizationConstruction p)

local instance PolarizationConstruction.ReferencePolarizationConstruction.dual_product_integral : IsIntegral (N.abelianScheme.scheme ⊗ N.abelianScheme.scheme).left := by
  let : IsIntegral N.abelian.toOver.left := N.abelian.variety.property
  let : Smooth N.abelian.toOver.hom := N.abelian.variety.presentation.smooth
  let : GeometricallyIntegral N.abelian.toOver.hom := AbelianIntegrality.abelian_geometricallyIntegral N.abelian
  let : IsLocallyNoetherian N.abelian.toOver.left := LocallyOfFiniteType.isLocallyNoetherian N.abelian.toOver.hom
  exact inferInstanceAs (IsIntegral (Limits.pullback N.abelian.toOver.hom N.abelian.toOver.hom))

def PolarizationConstruction.ReferencePolarizationConstruction.nativeDualAction (a : NumberField.RingOfIntegers E) : N.abelian.toOver ⟶ N.abelian.toOver :=
  AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback C.dual C.dual (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelianScheme.scheme (M.functorAction a))

instance PolarizationConstruction.ReferencePolarizationConstruction.nativeDualAction_isMonHom (a : NumberField.RingOfIntegers E) : IsMonHom (C.nativeDualAction a) := by
  let : IsIntegral (C.dual.abelian.scheme ⊗ C.dual.abelian.scheme).left :=
    inferInstanceAs (IsIntegral (N.abelianScheme.scheme ⊗ N.abelianScheme.scheme).left)
  exact Intrinsic.PoincareDual.nativePoincareDual_isMonHom C.dual C.dual (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelianScheme.scheme (M.functorAction a))

theorem PolarizationConstruction.ReferencePolarizationConstruction.nativeDualAction_poincare (a : NumberField.RingOfIntegers E) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 N.abelian.toOver ⊗ₘ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (C.nativeDualAction a ⊗ₘ 𝟙 M.abelian.toOver).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) :=
  Intrinsic.PoincareDual.nativePoincareDual_pullback_class C.dual C.dual
    (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelianScheme.scheme (M.functorAction a))

theorem PolarizationConstruction.ReferencePolarizationConstruction.nativeDualAction_intertwining (a : NumberField.RingOfIntegers E) :
    p.isogeny.hom ≫ C.nativeDualAction a =
      AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
        (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a)) ≫ p.isogeny.hom := by
  let f : M.abelian.toOver ⟶ M.abelian.toOver := AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)
  let r : M.abelian.toOver ⟶ M.abelian.toOver := AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
    (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a))
  let l : M.abelian.toOver ⟶ N.abelian.toOver := p.isogeny.hom
  apply C.periodPairing_detects_group_maps M.abelian
  intro x y
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp]
  have ha := LinePeriodPairing.linePeriodPairing_adjoint N.abelian M.abelian (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)
    (C.nativeDualAction a) f (C.nativeDualAction_poincare a).symm (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift l x) y
  change C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.nativeDualAction a) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift l x)) y =
    C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift l (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift r x)) y
  change C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.nativeDualAction a) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift l x)) y =
    C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift l x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) at ha
  rw [ha, C.periodPairing_isogeny, C.periodPairing_isogeny]
  have h := C.chernForm_adjoint (NumberField.IsCMField.ringOfIntegersComplexConj E a) x y
  have hc : NumberField.IsCMField.ringOfIntegersComplexConj E
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) = a := by
    apply NumberField.RingOfIntegers.ext
    exact NumberField.IsCMField.complexConj_apply_apply E a
  rw [hc] at h
  exact h.symm

theorem PolarizationConstruction.ReferencePolarizationConstruction.pelFamily_rosati (level : ℕ) [NeZero level] :
    (C.pelFamily level).IsRosatiCompatible
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom := by
  intro a
  refine ⟨AlgebraicGeometry.AbelianScheme.TateComparison.End.endOfSchemeMap N.abelian.toOver (C.nativeDualAction a), ?_, ?_⟩
  · change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (𝟙 N.abelian.toOver ⊗ₘ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)).left
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap N.abelian.toOver (AlgebraicGeometry.AbelianScheme.TateComparison.End.endOfSchemeMap N.abelian.toOver (C.nativeDualAction a)) ⊗ₘ
          𝟙 M.abelian.toOver).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap]
    exact C.nativeDualAction_poincare a
  · change p.isogeny.hom ≫
        AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap N.abelian.toOver (AlgebraicGeometry.AbelianScheme.TateComparison.End.endOfSchemeMap N.abelian.toOver (C.nativeDualAction a)) =
      AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
        (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a)) ≫ p.isogeny.hom
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap]
    exact C.nativeDualAction_intertwining a

theorem PolarizationConstruction.ReferencePolarizationConstruction.pelFamily_isPEL (level : ℕ) [NeZero level] :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.IsPELFamily P (LieSignature.referenceComplexBaseAction P) (C.pelFamily level) :=
  ⟨⟨C.pelFamily_kernelType level, C.pelFamily_positive level, C.pelFamily_rosati level⟩,
    C.pelFamily_signature level⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Reference
