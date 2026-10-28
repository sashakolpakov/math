import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentBijection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalMap

/-! # Represented Picard Tangent Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentMorphism

noncomputable section

/-! The constructed Picard tangent comparison is natural for actual
Poincare duals, using the original native group differential and H1 pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)

local instance picardMorphismIntegral {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) : IsIntegral G.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G
local instance picardMorphismDiagonal {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ G.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal G.scheme
local instance picardMorphismH1Module (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule G.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule G

variable (f : A.scheme ⟶ B.scheme) (d : DB.abelian.scheme ⟶ DA.abelian.scheme) [IsMonHom d]
    (hp : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare))

include hp

theorem representedPicardTangentLinear_morphism
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension DB.abelian.scheme.hom) → ℂ) :
    RepresentedPicardTangentBijection.representedPicardTangentLinear A DA (Intrinsic.GroupConormalMap.nativeGroupTangentMap d v) =
      StructurePullbackLinear.nativeStructureH1PullbackLinear f (RepresentedPicardTangentBijection.representedPicardTangentLinear B DB v) := by
  have ht : Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv DA.abelian.scheme 1 (Intrinsic.GroupConormalMap.nativeGroupTangentMap d v) =
      Dual.ParameterPoincareSquare.dualPointPostcompose d (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv DB.abelian.scheme 1 v) :=
    Subtype.ext (Intrinsic.GroupConormalMap.nativeGroupTangentMap_lift d v)
  change Dual.ParameterDeformationClass.dualParameterDeformationClass DA.poincare DA.normalizedAtDualZero.some
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv DA.abelian.scheme 1 (Intrinsic.GroupConormalMap.nativeGroupTangentMap d v)) =
    StructurePullback.nativeStructureH1Pullback f (Dual.ParameterDeformationClass.dualParameterDeformationClass DB.poincare DB.normalizedAtDualZero.some
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv DB.abelian.scheme 1 v))
  rw [ht]
  exact Dual.ParameterClassMorphism.dualParameterDeformationClass_morphism f d DA.poincare DB.poincare
    DA.normalizedAtDualZero.some DB.normalizedAtDualZero.some hp
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv DB.abelian.scheme 1 v)

theorem representedPicardTangentLinear_morphism_comp :
    (RepresentedPicardTangentBijection.representedPicardTangentLinear A DA).comp (Intrinsic.GroupConormalMap.nativeGroupTangentMap d) =
      (StructurePullbackLinear.nativeStructureH1PullbackLinear f).comp (RepresentedPicardTangentBijection.representedPicardTangentLinear B DB) :=
  LinearMap.ext (representedPicardTangentLinear_morphism A B DA DB f d hp)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentMorphism
