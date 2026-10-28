import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-! # Point Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointNormalization

noncomputable section

/-! An actual dual point gives its Poincare line with zero-section normalization over any parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  {T : Over S} (x : T ⟶ D.abelian)

/-- The actual Poincare line corresponding to the given dual point. -/
def line : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (x ▷ A).left D.poincare

/-- Pulling the dual normalization along the point gives the actual zero-section frame. -/
def zeroFrame : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj (line D x).sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left := by
  let z : T ⟶ T ⊗ A := lift (𝟙 T) 1
  let zD : D.abelian ⟶ D.abelian ⊗ A := lift (𝟙 D.abelian) 1
  have h : z ≫ (x ▷ A) = x ≫ zD := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [z, zD]
  exact (Scheme.Modules.pullbackComp z.left (x ▷ A).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app D.poincare.sheaf ≪≫
    ((Scheme.Modules.pullbackComp x.left zD.left).app D.poincare.sheaf).symm ≪≫
    (Scheme.Modules.pullback x.left).mapIso (Classical.choice D.normalizedAtAbelianZero) ≪≫
    Line.Bundles.pullbackUnitIso x.left

/-- The line class is exactly the actual Poincare class of the dual point. -/
theorem picardClass : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (line D x)) = Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D x := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointNormalization
