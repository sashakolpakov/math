import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.Translation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationLineKernelCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphTranslationKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.TangentIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Polarization Graph Log -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphLog.Construction

noncomputable section

/-! The original line-logarithm class for a polarized family's
canonical graph bundle is twice the original polarization tangent
class. The graph-bundle base-change isomorphism is used explicitly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable (R : Type) [CommRing R] [Algebra R ℂ]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover A.graphBundle)

local instance graphLogH1Module :
    Module ℂ (SheafCohomology.AffineH.Projective.H (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).abelian.scheme.left) 1) :=
  AbelianModuli.ReferenceFamily.StructureComplexScalars.structureH1ComplexModule
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).abelian.scheme

theorem polarizationGraphLineLogSheafClass_native
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme).hom) → ℂ) :
    AbelianModuli.ReferenceFamily.FixedFiber.LineLogIntrinsicClass.fixedFiberLineLogSheafClass R A.abelian.scheme C.cover C.transitions
      (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear (AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme) v) =
      (2 : ℂ) • AbelianModuli.ReferenceFamily.Polarized.TangentEquiv.polarizedStructureH1TangentEquiv
        (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) v := by
  let G := AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber ℂ R A.abelian.scheme
  let p := AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ A.abelian.scheme
  let f := Spec.map (CommRingCat.ofHom (algebraMap R ℂ))
  let A₀ := A.pullback f
  let t := AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v
  have hline : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.graphBundle.pullback p) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A₀.graphBundle :=
    Quotient.sound ⟨(A.graphBundle_baseChangeIso f).symm⟩
  have hkernel := TranslationLineKernelCongruence.Construction.dualTranslationLineKernel_congr G (A.graphBundle.pullback p)
    A₀.graphBundle hline t
  rw [FixedFiber.Translation.Construction.fixedFiberLineLogSheafClass_eq_translation R A.abelian.scheme A.graphBundle C v, hkernel]
  exact AbelianModuli.ReferenceFamily.Polarization.GraphTranslationKernel.polarizationGraphTranslationClass_native A₀ v

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationGraphLog.Construction
