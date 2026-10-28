import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.SheafBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionAdjoint

/-! # Base Change Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeComposition

noncomputable section

/-! Canonical structure-sheaf base change is compatible with successive Cartesian base changes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y Z P Q : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} {c : Q ⟶ P} {d : Q ⟶ Z} {h : Z ⟶ Y}
    (H : IsPullback a b f g) (J : IsPullback c d b h)

theorem structureBaseChangeAdjoint_paste :
    SheafBaseChange.structureBaseChangeAdjoint H ≫
        (Scheme.Modules.pushforward g).map (SheafBaseChange.structureBaseChangeAdjoint J) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app
          ((Scheme.Modules.pushforward d).obj (Line.Bundles.structureModule Q)) =
      SheafBaseChange.structureBaseChangeAdjoint (J.paste_horiz H) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change (SheafBaseChange.structureBaseChangeAdjoint J).app (g ⁻¹ᵁ U)
      ((SheafBaseChange.structureBaseChangeAdjoint H).app U s) =
    (SheafBaseChange.structureBaseChangeAdjoint (J.paste_horiz H)).app U s
  have h₁ := SheafBaseChange.structureBaseChangeAdjoint_app J (g ⁻¹ᵁ U)
    ((SheafBaseChange.structureBaseChangeAdjoint H).app U s)
  have h₂ := congrArg
    (fun z : Γ(P, b ⁻¹ᵁ (g ⁻¹ᵁ U)) => c.appLE (b ⁻¹ᵁ (g ⁻¹ᵁ U))
      ((d ≫ h) ⁻¹ᵁ (g ⁻¹ᵁ U)) (PushforwardMorphism.overMorphism_preimage_le c (d ≫ h) b J.w (g ⁻¹ᵁ U)) z)
    (SheafBaseChange.structureBaseChangeAdjoint_app H U s)
  have h₃ := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE c a (f ⁻¹ᵁ U) (b ⁻¹ᵁ (g ⁻¹ᵁ U))
      ((d ≫ h) ⁻¹ᵁ (g ⁻¹ᵁ U))
      (PushforwardMorphism.overMorphism_preimage_le a (b ≫ g) f H.w U)
      (PushforwardMorphism.overMorphism_preimage_le c (d ≫ h) b J.w (g ⁻¹ᵁ U))) s
  exact h₁.trans (h₂.trans (h₃.trans (SheafBaseChange.structureBaseChangeAdjoint_app (J.paste_horiz H) U s).symm))

theorem structureBaseChangeMap_paste :
    (Scheme.Modules.pullbackComp h g).inv.app
        ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)) ≫
      (Scheme.Modules.pullback h).map (SheafBaseChange.structureBaseChangeMap H) ≫ SheafBaseChange.structureBaseChangeMap J =
      SheafBaseChange.structureBaseChangeMap (J.paste_horiz H) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).homEquiv _ _).injective
  rw [Pullback.CompositionAdjoint.pullbackComposition_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, SheafBaseChange.structureBaseChangeMap_normalization,
    Adjunction.homEquiv_naturality_right, SheafBaseChange.structureBaseChangeMap_normalization,
    SheafBaseChange.structureBaseChangeMap_normalization]
  exact structureBaseChangeAdjoint_paste H J

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeComposition
