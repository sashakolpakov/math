import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Relative
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference

/-! # Primitive Dual -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PrimitiveDual.Geometric

noncomputable section

/-! The original primitive ThetaConstruction theta line supplies actual HilbertConstruction dual
abelian data, with both identity normalizations and a positive isogeny.
The dual is constructed from the proved Picard representation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}

structure PrimitiveDualConstruction (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N) where
  ampleLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left
  poincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left
  homogeneous : M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf poincare)
  ample : ampleLine.IsAmple
  chern : ∀ l m : T.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian ampleLine
    (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)
  universal : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme poincare homogeneous)
  difference : (poincare.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
    (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme ampleLine).sheaf
  dualZero : (poincare.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
    (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left
  abelianZero : (poincare.pullback (lift (𝟙 N.abelianScheme.scheme)
    (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left

theorem primitiveDualConstruction_nonempty (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)
    (hE : E.transpose = -E) : Nonempty (PrimitiveDualConstruction p) := by
  obtain ⟨L, Q, hQ, hL, hchern, hiso, ⟨ed⟩, ⟨en⟩, ⟨ea⟩⟩ :=
    p.exists_primitive_relative_picard_classification hE
  exact ⟨⟨L, Q, hQ, hL, hchern, hiso, ed, en, ea⟩⟩

namespace PrimitiveDualConstruction
variable {p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N} (C : PrimitiveDualConstruction p)

def dual : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData M.abelianScheme :=
  letI := C.universal
  RepresentationTheory.Theta.Geometric.Dual.PicardData.dualDataOfHomogeneousParameterIso M.abelianScheme N.abelianScheme C.poincare C.homogeneous
    C.abelianZero C.dualZero

theorem positive (K : Type) [Field K] [IsAlgClosed K] (z : Spec (.of K) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber C.dual p.isogeny.hom K z :=
  RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference.positiveOnGeometricFiber_of_difference_iso C.dual p.isogeny C.ampleLine C.ample C.difference K z

end PrimitiveDualConstruction

theorem exists_primitive_dual_on_actual_model (M : PeriodModel.Geometric.AlgebraicPeriodModel T)
    (hE : E.transpose = -E) :
    ∃ (N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T) (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N),
      Nonempty (PrimitiveDualConstruction p) := by
  obtain ⟨N, ⟨p⟩⟩ := IntegralDualIsogenyKernel.Geometric.exists_integralDualLatticeIsogeny M
  exact ⟨N, p, primitiveDualConstruction_nonempty p hE⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PrimitiveDual.Geometric
