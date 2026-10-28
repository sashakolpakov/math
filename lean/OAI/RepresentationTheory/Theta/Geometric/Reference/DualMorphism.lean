import OAI.RepresentationTheory.Theta.Geometric.Reference.PoincareDetection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareClass

/-! # Dual Morphism -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference

noncomputable section

/-! The represented dual of a reference group morphism has the actual
Poincare identity and the exact adjoint identity on rational periods. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    (C : PolarizationConstruction.ReferencePolarizationConstruction p) (C' : PolarizationConstruction.ReferencePolarizationConstruction p')
    (f : M.abelianScheme.scheme ⟶ M'.abelianScheme.scheme) [IsMonHom f]

def PolarizationConstruction.ReferencePolarizationConstruction.referenceDualMap : N'.abelianScheme.scheme ⟶ N.abelianScheme.scheme :=
  AlgebraicGeometry.Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback C.dual C'.dual f

instance PolarizationConstruction.ReferencePolarizationConstruction.referenceDualMap_isMonHom : IsMonHom (C.referenceDualMap C' f) :=
  AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism.dualPicardPullback_preserves_given_group C.dual C'.dual f

theorem PolarizationConstruction.ReferencePolarizationConstruction.referenceDualMap_poincare :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (C.referenceDualMap C' f ⊗ₘ 𝟙 M.abelianScheme.scheme).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 N'.abelianScheme.scheme ⊗ₘ f).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) :=
  AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareClass.dualPicardPullback_actual_poincare C.dual C'.dual f

theorem PolarizationConstruction.ReferencePolarizationConstruction.referenceDualMap_periodPairing (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods N'.abelian) (y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.referenceDualMap C' f) x) y =
      C'.periodPairing x (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) := by
  have hl := LinePeriodPairing.linePeriodPairing_pullback N'.abelian M.abelian N.abelian M.abelian
    (C.referenceDualMap C' f) (𝟙 M.abelian.toOver) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) x y
  have hr := LinePeriodPairing.linePeriodPairing_pullback N'.abelian M.abelian N'.abelian M'.abelian
    (𝟙 N'.abelian.toOver) f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) x y
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hl hr
  exact hl.symm.trans ((congrArg (fun L => LinePeriodPairing.linePeriodPairing N'.abelian M.abelian L x y)
    (C.referenceDualMap_poincare C' f)).trans hr)

end

end OAI.RepresentationTheory.Theta.Geometric.Reference
