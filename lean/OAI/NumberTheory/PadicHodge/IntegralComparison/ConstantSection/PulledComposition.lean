import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction

/-! # Pulled Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.PulledComposition

noncomputable section

/-! Pullback of the original constant-module section map respects postcomposition. -/

open _root_.CategoryTheory

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u} R, F.op.HasPointwiseRightKanExtension P]
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  {N L : CochainComplex (Sheaf K (ModuleCat.{u} R)) ℕ}
  (a : ((constantSheaf K (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶ N)
  (b : N ⟶ L)

theorem component (i : ℕ) :
    (ComplexRestriction.pulled F R J K M L (a ≫ b)).f i =
      (ComplexRestriction.pulled F R J K M N a).f i ≫
        (F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).map (b.f i) := by
  let T := F.sheafPushforwardContinuous (ModuleCat.{u} R) J K
  change _ ≫ T.map (a.f i ≫ b.f i) = (_ ≫ T.map (a.f i)) ≫ T.map (b.f i)
  rw [T.map_comp]
  exact (Category.assoc _ _ _).symm

theorem map : ComplexRestriction.pulled F R J K M L (a ≫ b) =
    ComplexRestriction.pulled F R J K M N a ≫
      ((F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).mapHomologicalComplex (.up ℕ)).map b := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component F R J K M a b i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.PulledComposition
