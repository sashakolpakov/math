import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareLine
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Rigidified Point Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPointFrames.Construction

noncomputable section

/-! An actual identity-axis rigidification supplies coherent zero
frames for all point lines, including the origin of group parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u
variable {k : Type u} [Field k] {A C : Over (Spec (.of k))} [GrpObj A] [GrpObj C]
  (Q : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A C)

def rigidifiedProductZeroFrame (U : Over (Spec (.of k))) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) (1 : U ⟶ C ⊗ A) :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (lift (𝟙 C) (1 : C ⟶ A)) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) Q.axis.symm (1 : U ⟶ C) 1 (by
    apply CartesianMonoidalCategory.hom_ext <;> simp)

theorem rigidifiedProductZeroFrame_natural {U V : Over (Spec (.of k))} (r : V ⟶ U) :
    Picard.PoincareBundle.FrameRatioPullback.pullFrame r.left (rigidifiedProductZeroFrame Q U) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) r 1 1 (MonObj.comp_one r) =
        rigidifiedProductZeroFrame Q V :=
  Picard.PoincareBundle.GlobalFrameNaturality.atPoint_pullback
    (lift (𝟙 C) (1 : C ⟶ A)) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) Q.axis.symm r 1 1
    (by apply CartesianMonoidalCategory.hom_ext <;> simp)
    1 1 (by apply CartesianMonoidalCategory.hom_ext <;> simp) (MonObj.comp_one r) (MonObj.comp_one r)

def rigidifiedPointLine {T : Over (Spec (.of k))} (x : T ⟶ C) (a : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left :=
  Q.bundle.pullback (lift x a).left

def rigidifiedPointOriginFrame {T : Over (Spec (.of k))} [GrpObj T]
    (x : T ⟶ C) (a : T ⟶ A) [IsMonHom x] [IsMonHom a] :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((rigidifiedPointLine Q x a).pullback η[T].left).sheaf :=
  rigidifiedProductZeroFrame Q _ ≪≫
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison (lift x a) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q.bundle) η[T] 1
      (by rw [MonObj.one_eq_one]; exact MonObj.one_comp (lift x a))).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPointFrames.Construction
