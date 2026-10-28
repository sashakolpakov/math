import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardBaseComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.SheafBaseChange

/-! # Base Change Equivariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeEquivariance

noncomputable section

/-! The canonical structure-sheaf base-change map intertwines actual commuting endomorphisms of a Cartesian square. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g)
    (u : X ⟶ X) (v : P ⟶ P) (hu : u ≫ f = f) (hv : v ≫ b = b)
    (hva : v ≫ a = a ≫ u)

include hva

theorem structureBaseChangeAdjoint_intertwines :
    PushforwardMorphism.structurePushforwardOverMorphism u f f hu ≫ SheafBaseChange.structureBaseChangeAdjoint H =
      SheafBaseChange.structureBaseChangeAdjoint H ≫
        (Scheme.Modules.pushforward g).map (PushforwardMorphism.structurePushforwardOverMorphism v b b hv) := by
  let t := b ≫ g
  have hvg : v ≫ t = t :=
    (Category.assoc v b g).symm.trans (congrArg (fun z => z ≫ g) hv)
  let σ := PushforwardMorphism.structurePushforwardOverMorphism u f f hu
  let τ := PushforwardMorphism.structurePushforwardOverMorphism v b b hv
  let ν := PushforwardMorphism.structurePushforwardOverMorphism v t t hvg
  let γ := PushforwardMorphism.structurePushforwardOverMorphism a t f H.w
  let α := SheafBaseChange.structureBaseChangeAdjoint H
  let e := (Scheme.Modules.pushforwardComp b g).app (Line.Bundles.structureModule P)
  have hs : σ ≫ γ = γ ≫ ν :=
    (PushforwardFunctor.structurePushforwardOverMorphism_comp a u t f f H.w hu).trans
      ((PushforwardBaseComposition.structurePushforwardOverMorphism_congr (a ≫ u) (v ≫ a) t f _ _ hva.symm).trans
        (PushforwardFunctor.structurePushforwardOverMorphism_comp v a t t f hvg H.w).symm)
  have hn : (Scheme.Modules.pushforward g).map τ ≫ e.hom = e.hom ≫ ν :=
    PushforwardBaseComposition.structurePushforwardOverMorphism_pushforward_comp v b b g hv
  have hα : α ≫ e.hom = γ := by
    simp only [α, e, SheafBaseChange.structureBaseChangeAdjoint, Category.assoc]
    rfl
  apply (cancel_mono e.hom).mp
  change (σ ≫ α) ≫ e.hom = (α ≫ (Scheme.Modules.pushforward g).map τ) ≫ e.hom
  calc
    (σ ≫ α) ≫ e.hom = σ ≫ γ := by rw [Category.assoc, hα]
    _ = γ ≫ ν := hs
    _ = (α ≫ e.hom) ≫ ν := congrArg (fun z => z ≫ ν) hα.symm
    _ = (α ≫ (Scheme.Modules.pushforward g).map τ) ≫ e.hom := by
      rw [Category.assoc, ← hn, ← Category.assoc]

theorem structureBaseChangeMap_intertwines :
    (Scheme.Modules.pullback g).map (PushforwardMorphism.structurePushforwardOverMorphism u f f hu) ≫
        SheafBaseChange.structureBaseChangeMap H =
      SheafBaseChange.structureBaseChangeMap H ≫ PushforwardMorphism.structurePushforwardOverMorphism v b b hv := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    SheafBaseChange.structureBaseChangeMap_normalization]
  exact structureBaseChangeAdjoint_intertwines H u v hu hv hva

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeEquivariance
