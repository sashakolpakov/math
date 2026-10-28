import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareParameterPullbackPair
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentBijection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullbackLinear

/-! # Additive Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AdditivePullback

noncomputable section

/-! Pullback on original structure-sheaf H1 is additive in maps
to an abelian scheme. Every class is an actual Poincare tangent class,
so this follows from the original multiplicative pairing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {n : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)

local instance additivePicardIntegral {m : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme m Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsIntegral G.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G
local instance additivePicardDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal A.scheme
local instance additivePullbackH1Module (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule Y.left) 1) := StructureComplexScalars.structureH1ComplexModule Y

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

include D P

theorem nativeStructureH1Pullback_mul (f g : X ⟶ A.scheme)
    (c : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) :
    StructurePullback.nativeStructureH1Pullback (f * g) c = StructurePullback.nativeStructureH1Pullback f c + StructurePullback.nativeStructureH1Pullback g c := by
  obtain ⟨v, rfl⟩ := (RepresentedPicardTangentBijection.representedPicardTangentLinear_bijective A D P).surjective c
  let q := Dual.ParameterLineKernel.dualParameterLineKernel D.poincare D.normalizedAtDualZero.some
    (SchemeDualTangent.nativeSchemeTangentDualEquiv D.abelian.scheme 1 v)
  change StructurePullback.nativeStructureH1Pullback (f * g) (DualLine.ClassKernel.dualLineKernelCohomology A.scheme q) =
    StructurePullback.nativeStructureH1Pullback f (DualLine.ClassKernel.dualLineKernelCohomology A.scheme q) +
      StructurePullback.nativeStructureH1Pullback g (DualLine.ClassKernel.dualLineKernelCohomology A.scheme q)
  rw [← DualLine.ClassMorphism.dualLineKernelCohomology_morphism (f * g), PoincareParameterPullbackPair.dualPoincareParameter_pullback_mul,
    DualLine.ClassKernel.dualLineKernelCohomology_mul, DualLine.ClassMorphism.dualLineKernelCohomology_morphism,
    DualLine.ClassMorphism.dualLineKernelCohomology_morphism]

theorem nativeStructureH1PullbackLinear_mul (f g : X ⟶ A.scheme) :
    StructurePullbackLinear.nativeStructureH1PullbackLinear (f * g) =
      StructurePullbackLinear.nativeStructureH1PullbackLinear f + StructurePullbackLinear.nativeStructureH1PullbackLinear g :=
  LinearMap.ext (nativeStructureH1Pullback_mul A D P f g)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AdditivePullback
