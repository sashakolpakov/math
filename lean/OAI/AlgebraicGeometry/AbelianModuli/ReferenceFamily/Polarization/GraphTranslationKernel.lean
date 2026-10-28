import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PairSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareDualPairCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.TranslationKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Graph Translation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphTranslationKernel

noncomputable section

/-! The actual polarization graph bundle has infinitesimal
translation class equal to twice the original polarization tangent
class. The proof expands the original multiplicative Poincare pairing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

local instance polarizationGraphPicardGroup (X : Scheme.{0}) : CommGroup (HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :=
  Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard.instCommGroupIsoClass

variable {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarizationGraph_translation_class (t : DualOpen.Lifts.DualSchemePoints A.abelian.scheme 1) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (A.graphBundle.pullback (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation A.abelian.scheme t).left) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass A.dual.poincare (t.val ≫ A.polarization.isogeny.hom) ^ 2 *
        HilbertConstruction.Line.Bundles.LineBundle.classOf (A.graphBundle.pullback (snd (LieRanks.dualNumberTest ℂ) A.abelian.scheme).left) := by
  let T := LieRanks.dualNumberTest ℂ ⊗ A.abelian.scheme
  let u : T ⟶ A.abelian.scheme := fst (LieRanks.dualNumberTest ℂ) A.abelian.scheme ≫ t.val
  let b : T ⟶ A.abelian.scheme := snd (LieRanks.dualNumberTest ℂ) A.abelian.scheme
  let p := A.polarization.isogeny.hom
  let B := A.dual.poincarePairClass T
  let q := RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass A.dual.poincare (t.val ≫ p)
  have h₀ : B (u ≫ p) u = 1 := by
    change A.dual.poincarePairClass T ((fst (LieRanks.dualNumberTest ℂ) A.abelian.scheme ≫ t.val) ≫ p) u = 1
    rw [Category.assoc]
    exact PoincareDualPairCoordinates.poincareDualBasePair_trivial A.abelian A.dual (t.val ≫ p) t.val
  have hcross : B (u ≫ p) b = q := by
    change A.dual.poincarePairClass T ((fst (LieRanks.dualNumberTest ℂ) A.abelian.scheme ≫ t.val) ≫ p) b = q
    rw [Category.assoc]
    exact (PoincareDualPairCoordinates.poincareParameterLineClass_eq_pair A.abelian A.dual (t.val ≫ p)).symm
  have hsymm : B (b ≫ p) u = B (u ≫ p) b := PairSymmetry.polarizationPair_class_symm A T b u
  have hb : HilbertConstruction.Line.Bundles.LineBundle.classOf (A.graphBundle.pullback b.left) = B (b ≫ p) b :=
    Quotient.sound ⟨A.dual.poincareGraphPullbackPairIso p b⟩
  calc
    _ = B ((u * b) ≫ p) (u * b) :=
      Quotient.sound ⟨A.dual.poincareGraphPullbackPairIso p (u * b)⟩
    _ = (B (u ≫ p) u * B (u ≫ p) b) * (B (b ≫ p) u * B (b ≫ p) b) := by
      rw [MonObj.mul_comp, B.map_mul]
      change B (u ≫ p) (u * b) * B (b ≫ p) (u * b) = _
      rw [(B (u ≫ p)).map_mul, (B (b ≫ p)).map_mul]
    _ = q ^ 2 * B (b ≫ p) b := by
      rw [h₀, hsymm, hcross, one_mul, pow_two]
      exact (mul_assoc q q (B (b ≫ p) b)).symm
    _ = _ := congrArg (fun z => q ^ 2 * z) hb.symm

theorem polarizationGraphTranslationKernel_eq (t : DualOpen.Lifts.DualSchemePoints A.abelian.scheme 1) :
    Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel A.abelian.scheme A.graphBundle t =
      Dual.ParameterLineKernel.dualParameterLineKernel A.dual.poincare A.dual.normalizedAtDualZero.some
        (Dual.ParameterPoincareSquare.dualPointPostcompose A.polarization.isogeny.hom t) ^ 2 := by
  apply Subtype.ext
  calc
    _ = HilbertConstruction.Line.Bundles.LineBundle.classOf (A.graphBundle.pullback
        (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation A.abelian.scheme t).left) /
        HilbertConstruction.Line.Bundles.LineBundle.classOf (A.graphBundle.pullback
          (snd (LieRanks.dualNumberTest ℂ) A.abelian.scheme).left) :=
      DualLine.PullbackDifference.dualLinePullbackDifferenceKernel_class A.abelian.scheme
        (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation A.abelian.scheme t).left
        (snd (LieRanks.dualNumberTest ℂ) A.abelian.scheme).left
        (Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction A.abelian.scheme t) A.graphBundle
    _ = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass A.dual.poincare (t.val ≫ A.polarization.isogeny.hom) ^ 2 :=
      (eq_div_of_mul_eq' (polarizationGraph_translation_class A t).symm).symm
    _ = _ := rfl

local instance graphTranslationIntegral {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsIntegral G.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G
local instance graphTranslationDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.abelian.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal A.abelian.scheme
local instance graphTranslationH1Module : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.abelian.scheme

theorem polarizationGraphTranslationClass_native
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) :
    DualLine.ClassKernel.dualLineKernelCohomology A.abelian.scheme
      (Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel A.abelian.scheme A.graphBundle
        (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.abelian.scheme 1 v)) =
      (2 : ℂ) • Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A v := by
  let t := Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.abelian.scheme 1 v
  let q := Dual.ParameterLineKernel.dualParameterLineKernel A.dual.poincare A.dual.normalizedAtDualZero.some
    (Dual.ParameterPoincareSquare.dualPointPostcompose A.polarization.isogeny.hom t)
  have hq : DualLine.ClassKernel.dualLineKernelCohomology A.abelian.scheme q = Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A v :=
    (congrArg (DualLine.ClassKernel.dualLineKernelCohomology A.abelian.scheme) (TranslationKernel.polarizationLineTranslationKernel_eq A t)).symm.trans
      (TranslationKernel.polarizationLineTranslationClass_native A v)
  rw [polarizationGraphTranslationKernel_eq, pow_two, DualLine.ClassKernel.dualLineKernelCohomology_mul, hq]
  exact (two_smul ℂ (Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A v)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.GraphTranslationKernel
