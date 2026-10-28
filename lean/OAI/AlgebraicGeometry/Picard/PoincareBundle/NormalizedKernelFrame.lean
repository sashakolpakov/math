import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.FamilyKernel
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyZeroRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness

/-! # Normalized Kernel Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelFrame

noncomputable section

/-! The actual represented kernel has a canonically normalized trivialization of its family line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A T H : Over S} [GrpObj A]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (m : T ⟶ D.abelian) (h : H ⟶ T)
  (R : Line.Bundles.LineBundle (T ⊗ A).left)
  (e : R.sheaf ≅ (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) m).sheaf)
  (hh : h ≫ m = 1)
  (eR : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj R.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

/-- Normalize the actual kernel trivialization using the given zero frame of the original family. -/
def frame : (Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).obj R.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left :=
  Isogenies.NeighborCounting.RigidifiedIso.normalizedIso (fst H A).left (lift (𝟙 H) (1 : H ⟶ A)).left
    (Poincare.FamilyKernel.Family.kernelFrame D m h R e hh)
    (FamilyZeroRestriction.Family.zeroFrame h R eR)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (lift (𝟙 H) (1 : H ⟶ A)).left)

/-- The constructed frame has exactly the restriction of the original family's zero normalization. -/
theorem frame_normalized :
    (Scheme.Modules.pullback (lift (𝟙 H) (1 : H ⟶ A)).left).map (frame D m h R e hh eR).hom ≫
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (lift (𝟙 H) (1 : H ⟶ A)).left).hom =
        (FamilyZeroRestriction.Family.zeroFrame h R eR).hom :=
  Isogenies.NeighborCounting.RigidifiedIso.normalizedIso_section (fst H A).left (lift (𝟙 H) (1 : H ⟶ A)).left
    (congrArg Over.Hom.left (lift_fst (𝟙 H) (1 : H ⟶ A)))
    (Poincare.FamilyKernel.Family.kernelFrame D m h R e hh)
    (FamilyZeroRestriction.Family.zeroFrame h R eR)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (lift (𝟙 H) (1 : H ⟶ A)).left)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelFrame
