import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComparison

/-! # Tensor Composition Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The pullback composition comparison respects the units used by tensor pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem Pullback.TensorCompositionUnits.pullbackComp_hom_unit (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M)) ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackComp f g).hom.app M)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M) =
        (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  let L := Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f
  let R := Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g
  let adj := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let e := Scheme.Modules.pullbackComp f g
  let b := Scheme.Modules.pushforwardComp f g
  have hu : adj.unit.app M ≫ b.hom.app (L.obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map (e.inv.app M) := by
    have h := unit_conjugateEquiv adj
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) e.inv M
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
    exact h
  have he : e.inv.app M ≫ e.hom.app M = 𝟙 _ := e.inv_hom_id_app M
  change adj.unit.app M ≫ R.map (e.hom.app M) ≫
    b.hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M) = _
  rw [b.hom.naturality, ← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
    he, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

theorem Pullback.TensorCompositionUnits.pullbackComp_homEquiv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (P : X.Modules)
    (h : (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ P) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullbackComp f g).hom.app M ≫ h)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app P =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _ h := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn : (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map h) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app P =
      (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M) ≫
        (Scheme.Modules.pushforward (f ≫ g)).map h :=
    (Scheme.Modules.pushforwardComp f g).hom.naturality h
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun a => a ≫ (Scheme.Modules.pushforward (f ≫ g)).map h)
      (Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g M)

theorem Bilinear.Sheaves.SheafBilinearMap.pushforward_comp {M N P : X.Modules}
    (β : Bilinear.Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((β.pushforward f).pushforward g).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P) =
      (β.pushforward (f ≫ g)).precomp
        ((Scheme.Modules.pushforwardComp f g).hom.app M)
        ((Scheme.Modules.pushforwardComp f g).hom.app N) := by
  ext U
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
