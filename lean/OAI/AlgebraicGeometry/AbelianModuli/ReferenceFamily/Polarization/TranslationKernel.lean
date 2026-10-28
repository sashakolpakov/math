import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionTranslationLineKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Biextension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentEquiv

/-! # Translation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.TranslationKernel

noncomputable section

/-! Infinitesimal translation of the original ample polarization
bundle is exactly the original polarization followed by its represented
Picard tangent map. All equalities retain the actual line classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarizationBiextension_parameter_class (t : LieRanks.dualNumberTest ℂ ⟶ A.abelian.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Biextension.polarizationOriginalBiextension A) t =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass A.dual.poincare (t ≫ A.polarization.isogeny.hom) := by
  have h := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ⊗ₘ 𝟙 A.abelian.scheme).left)
    (Biextension.polarizationOriginalBiextension_class A)
  change RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Biextension.polarizationOriginalBiextension A) t =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ⊗ₘ 𝟙 A.abelian.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)) at h
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom, Category.id_comp] at h
  exact h

theorem polarizationLineTranslationKernel_eq (t : DualOpen.Lifts.DualSchemePoints A.abelian.scheme 1) :
    Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel A.abelian.scheme (Intrinsic.ChernPairing.polarizationLineBundle A) t =
      Dual.ParameterLineKernel.dualParameterLineKernel A.dual.poincare A.dual.normalizedAtDualZero.some
        (Dual.ParameterPoincareSquare.dualPointPostcompose A.polarization.isogeny.hom t) := by
  apply Subtype.ext
  let : CommGroup (HilbertConstruction.Line.Bundles.LineBundle.IsoClass (LieRanks.dualNumberTest ℂ ⊗ A.abelian.scheme).left) :=
    Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard.instCommGroupIsoClass
  calc
    _ = HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback
        (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation A.abelian.scheme t).left) /
        HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback
          (snd (LieRanks.dualNumberTest ℂ) A.abelian.scheme).left) :=
      DualLine.PullbackDifference.dualLinePullbackDifferenceKernel_class A.abelian.scheme
        (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation A.abelian.scheme t).left
        (snd (LieRanks.dualNumberTest ℂ) A.abelian.scheme).left
        (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction A.abelian.scheme t) (Intrinsic.ChernPairing.polarizationLineBundle A)
    _ = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Biextension.polarizationOriginalBiextension A) t.val :=
      (eq_div_of_mul_eq' (BiextensionTranslationLineKernel.biextension_dualTranslation_class A.abelian.scheme
        (Intrinsic.ChernPairing.polarizationLineBundle A) (Biextension.polarizationOriginalBiextension A)
        (Biextension.polarizationLineBundle_poincare A).some t)).symm
    _ = _ := polarizationBiextension_parameter_class A t.val

local instance polarizationTranslationIntegral {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsIntegral G.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G
local instance polarizationTranslationDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.abelian.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal A.abelian.scheme

theorem polarizationLineTranslationClass_native
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) :
    DualLine.ClassKernel.dualLineKernelCohomology A.abelian.scheme
      (Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel A.abelian.scheme (Intrinsic.ChernPairing.polarizationLineBundle A)
        (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.abelian.scheme 1 v)) = Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A v := by
  have ht : Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.dual.abelian.scheme 1
      (Intrinsic.GroupConormalMap.nativeGroupTangentMap A.polarization.isogeny.hom v) =
    Dual.ParameterPoincareSquare.dualPointPostcompose A.polarization.isogeny.hom (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.abelian.scheme 1 v) :=
    Subtype.ext (Intrinsic.GroupConormalMap.nativeGroupTangentMap_lift A.polarization.isogeny.hom v)
  change _ = DualLine.ClassKernel.dualLineKernelCohomology A.abelian.scheme
    (Dual.ParameterLineKernel.dualParameterLineKernel A.dual.poincare A.dual.normalizedAtDualZero.some
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.dual.abelian.scheme 1
        (Intrinsic.GroupConormalMap.nativeGroupTangentMap A.polarization.isogeny.hom v)))
  rw [ht, polarizationLineTranslationKernel_eq]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.TranslationKernel
