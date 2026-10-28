import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.UnitInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositeInjectivity

/-! # Open Pullback Section Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.OpenPullbackSectionInjectivity

noncomputable section

/-! A morphism that is an isomorphism over a nonempty open of an integral target pulls back line-bundle global sections injectively. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lineBundle_pullbackUnit_top_injective_of_common_open
    {X Y : Scheme.{u}} [IsIntegral Y] (q : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (U : Y.Opens) [Nonempty U] [IsIso (q ∣_ U)] :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app L.sheaf).app ⊤) := by
  let j : U.toScheme ⟶ X := inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι
  have hj : j ≫ q = U.ι := by
    change (inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι) ≫ q = U.ι
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  apply Pullback.UnitCompositeInjectivity.pullbackUnit_top_injective_of_composite j q L.sheaf
  exact (congrArg (fun f : U.toScheme ⟶ Y =>
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).app ⊤)) hj).mpr
      (L.openPullbackUnit_top_injective U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.OpenPullbackSectionInjectivity
