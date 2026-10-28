import OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackStalk

/-! # Stalk Unit Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkUnitNormalization.Local

noncomputable section

/-! The stalk-extension isomorphism intertwines the original
pullback adjunction unit and the tensor-product adjunction unit. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped IsMulCommutative

theorem stalkPointModuleSheafAdjunction_homEquiv {Z : TopCat.{0}}
    (T : Sheaf (Opens.grothendieckTopology Z) RingCat.{0}) (z : Z)
    (M : SheafOfModules.{0} T)
    (N : ModuleCat.{0} (TopCat.Presheaf.stalk (C := RingCat) (X := Z) T.obj z))
    (g : (StalkPointModuleAdjunction.Local.sheafRingModuleStalk T z).obj M ⟶ N) :
    (StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction T z).homEquiv M N g =
      (⟨StalkToPointModule.Local.stalkToPointModuleHom z M.val N g⟩ : M ⟶ (PointModuleFunctor.Local.pointModuleSheafFunctor T z).obj N) := by
  rw [StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
  {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{0}}
  [(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)]
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R) (x : X)
  [IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x)]
  [IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := Y) S.obj (f x))]
  {L : SheafOfModules.{0} S ⥤ SheafOfModules.{0} R}
  (adj : L ⊣ SheafOfModules.pushforward φ)

theorem moduleStalkIsoOfAdjunction_homEquiv (M : SheafOfModules.{0} S) :
    adj.homEquiv M _
        ((StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction R x).homEquiv (L.obj M) _
          ((PullbackStalk.Local.moduleStalkIsoOfAdjunction f φ x adj).hom.app M)) ≫
        (PointModulePushforward.Local.pointModuleSheafPushforward f φ x).hom.app _ =
      (StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction S (f x)).homEquiv M _
        ((ModuleCat.extendRestrictScalarsAdj
          (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x)).unit.app
          ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x)).obj M)) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((adj.comp (StalkPointModuleAdjunction.Local.stalkPointModuleSheafAdjunction R x)).ofNatIsoRight
      (PointModulePushforward.Local.pointModuleSheafPushforward f φ x))
    (PullbackStalk.Local.moduleStalkExtensionAdjunction f φ x) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  change _ = (PullbackStalk.Local.moduleStalkExtensionAdjunction f φ x).unit.app M at h
  refine h.trans ?_
  unfold PullbackStalk.Local.moduleStalkExtensionAdjunction
  rw [Adjunction.comp_unit_app, Adjunction.homEquiv_apply]

theorem moduleStalkIsoOfAdjunction_germ_unit (M : SheafOfModules.{0} S)
    (U : Opens Y) (hx : f x ∈ U) (m : M.val.obj (op U)) :
    (PullbackStalk.Local.moduleStalkIsoOfAdjunction f φ x adj).hom.app M
        (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) (L.obj M).val.presheaf
          ((Opens.map f).obj U) x hx ((adj.unit.app M).val.app (op U) m)) =
      (ModuleCat.extendRestrictScalarsAdj
          (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x)).unit.app
        ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x)).obj M)
          (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := Y) M.val.presheaf U (f x) hx m) := by
  have h := moduleStalkIsoOfAdjunction_homEquiv f φ x adj M
  rw [adj.homEquiv_apply] at h
  erw [stalkPointModuleSheafAdjunction_homEquiv,
    stalkPointModuleSheafAdjunction_homEquiv] at h
  let T := (ModuleCat.extendScalars
    (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x)).obj
      ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk S (f x)).obj M)
  exact congrArg (fun k : M ⟶ (PointModuleFunctor.Local.pointModuleSheafFunctor S (f x)).obj
      ((ModuleCat.restrictScalars (RingedStalkPushforward.Local.ringedStalkMap f (R := R.obj) (S := S.obj) φ.hom x)).obj T) =>
    (k.val.app (op U) m) ⟨hx⟩) h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkUnitNormalization.Local
