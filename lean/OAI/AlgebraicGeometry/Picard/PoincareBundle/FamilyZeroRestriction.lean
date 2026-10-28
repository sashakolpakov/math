import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Family Zero Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyZeroRestriction.Family

noncomputable section

/-! A family's specified zero frame restricts along every parameter morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

variable {S : Scheme.{u}} {A T H : Over S} [GrpObj A] (h : H ⟶ T)
  (R : Line.Bundles.LineBundle (T ⊗ A).left)
  (eR : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj R.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

/-- Parameter restriction commutes with the actual family-zero section. -/
theorem zero_square :
    lift (𝟙 H) (1 : H ⟶ A) ≫ (h ⊗ₘ 𝟙 A) = h ≫ lift (𝟙 T) (1 : T ⟶ A) := by
  simp

/-- The original zero frame restricts through the canonical geometric pullback comparisons. -/
def zeroFrame : (Scheme.Modules.pullback (lift (𝟙 H) (1 : H ⟶ A)).left).obj
    ((Scheme.Modules.pullback (h ⊗ₘ 𝟙 A).left).obj R.sheaf) ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left :=
  (Scheme.Modules.pullbackComp (lift (𝟙 H) (1 : H ⟶ A)).left (h ⊗ₘ 𝟙 A).left).app R.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (zero_square h))).app R.sheaf ≪≫
    (Scheme.Modules.pullbackComp h.left (lift (𝟙 T) (1 : T ⟶ A)).left).symm.app R.sheaf ≪≫
    (Scheme.Modules.pullback h.left).mapIso eR ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso h.left

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyZeroRestriction.Family
