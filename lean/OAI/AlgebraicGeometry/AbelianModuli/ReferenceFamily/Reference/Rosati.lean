import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PoincarePeriodPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizedConstruction
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodAdjoints

/-! # Rosati -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual represented dual of the integral CM action satisfies
the original Poincare equation and the reference polarization's Rosati equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} (C : PicardConstruction.ReferencePicardConstruction p)

local instance PicardConstruction.ReferencePicardConstruction.referenceDual_integral : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance PicardConstruction.ReferencePicardConstruction.referenceDual_smooth : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth
local instance PicardConstruction.ReferencePicardConstruction.referenceDual_productIntegral : IsIntegral (D.abelian.toOver ⊗ D.abelian.toOver).left :=
  (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety D.abelian.variety D.abelian.variety).property

def PicardConstruction.ReferencePicardConstruction.representedDualAction (a : NumberField.RingOfIntegers E) : D.abelian.toOver ⟶ D.abelian.toOver :=
  Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback C.dual C.dual (M.integralAction.map a)

instance PicardConstruction.ReferencePicardConstruction.representedDualAction_group (a : NumberField.RingOfIntegers E) : IsMonHom (C.representedDualAction a) := by
  let : IsIntegral (C.dual.abelian.scheme ⊗ C.dual.abelian.scheme).left :=
    inferInstanceAs (IsIntegral (D.abelian.toOver ⊗ D.abelian.toOver).left)
  exact RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual.nativePoincareDual_isMonHom C.dual C.dual (M.integralAction.map a)

theorem PicardConstruction.ReferencePicardConstruction.representedDualAction_poincare (a : NumberField.RingOfIntegers E) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (C.representedDualAction a ⊗ₘ 𝟙 M.abelian.toOver).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.toOver ⊗ₘ M.integralAction.map a).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) :=
  (RepresentationTheory.Theta.Geometric.Intrinsic.PoincareDual.nativePoincareDual_pullback_class C.dual C.dual (M.integralAction.map a)).symm

theorem PicardConstruction.ReferencePicardConstruction.representedDualAction_periodPairing (a : NumberField.RingOfIntegers E)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) (y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C.periodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.representedDualAction a) x) y =
      C.periodPairing x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) y) :=
  RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_adjoint D.abelian M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)
    (C.representedDualAction a) (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a))
    (C.representedDualAction_poincare a) x y

theorem PicardConstruction.ReferencePicardConstruction.representedDualAction_polarization (a : NumberField.RingOfIntegers E) :
    p.isogeny.hom ≫ C.representedDualAction a =
      M.integralAction.map (NumberField.IsCMField.ringOfIntegersComplexConj E a) ≫ p.isogeny.hom := by
  let b : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  let rho : M.abelian.toOver ⟶ M.abelian.toOver := AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
    (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a))
  let : IsMonHom b := inferInstanceAs (IsMonHom p.isogeny.hom)
  let : IsMonHom rho := inferInstanceAs (IsMonHom (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
    (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a))))
  let f := b ≫ C.representedDualAction a
  let g := rho ≫ b
  let : IsMonHom f := inferInstanceAs (IsMonHom (b ≫ C.representedDualAction a))
  let : IsMonHom g := inferInstanceAs (IsMonHom (rho ≫ b))
  change f = g
  apply C.periodPairing_detects_group_maps M.abelian f g
  intro x y
  dsimp only [f, g]
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [C.representedDualAction_periodPairing, C.periodPairing_isogeny, C.periodPairing_isogeny]
  have h := C.chernForm_adjoint (NumberField.IsCMField.ringOfIntegersComplexConj E a) x y
  rw [Polarization.PeriodAdjoints.integralConjugation_involutive] at h
  exact h.symm

theorem PicardConstruction.ReferencePicardConstruction.polarized_rosati (N : ℕ) [NeZero N] : ActionData.RosatiConjugation (C.polarized N) M.integralAction := by
  intro a
  exact ⟨C.representedDualAction a, C.representedDualAction_group a,
    C.representedDualAction_poincare a, C.representedDualAction_polarization a⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
