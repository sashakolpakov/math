import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundlePullbackUnit

/-! # Line Bundle Descent -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleDescent.Construction

noncomputable section

/-! Full faithfulness and isomorphism descent for line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def pullbackLineBundleHomEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) (M : Y.Modules)
    {N : Y.Modules} (hN : LineBundle.Construction.IsLineBundle N) :
    (M ⟶ N) ≃ ((Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) := by
  have := LineBundlePullbackUnit.Construction.isIso_pullbackUnit_of_isLineBundle f hf hN
  exact ((Iso.refl M).homCongr
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))).trans
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm

theorem pullbackLineBundleHomEquiv_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) {M N : Y.Modules}
    (hN : LineBundle.Construction.IsLineBundle N) (q : M ⟶ N) :
    pullbackLineBundleHomEquiv f hf M hN q = (Scheme.Modules.pullback f).map q := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm
      (𝟙 M ≫ q ≫ adj.unit.app N)) = _
  rw [Equiv.apply_symm_apply, Category.id_comp, Adjunction.homEquiv_unit]
  exact adj.unit.naturality q

theorem pullbackHom_bijective_of_isLineBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) (M : Y.Modules)
    {N : Y.Modules} (hN : LineBundle.Construction.IsLineBundle N) :
    Function.Bijective (fun q : M ⟶ N ↦ (Scheme.Modules.pullback f).map q) := by
  have he : (fun q : M ⟶ N ↦ (Scheme.Modules.pullback f).map q) =
      pullbackLineBundleHomEquiv f hf M hN :=
    funext fun q ↦ (pullbackLineBundleHomEquiv_apply f hf hN q).symm
  exact he.symm ▸ (pullbackLineBundleHomEquiv f hf M hN).bijective

def descendLineBundleIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) {M N : Y.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N)
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) : M ≅ N := by
  let a := (pullbackLineBundleHomEquiv f hf M hN).symm e.hom
  let b := (pullbackLineBundleHomEquiv f hf N hM).symm e.inv
  have ha : (Scheme.Modules.pullback f).map a = e.hom :=
    (pullbackLineBundleHomEquiv_apply f hf hN a).symm.trans
      ((pullbackLineBundleHomEquiv f hf M hN).apply_symm_apply e.hom)
  have hb : (Scheme.Modules.pullback f).map b = e.inv :=
    (pullbackLineBundleHomEquiv_apply f hf hM b).symm.trans
      ((pullbackLineBundleHomEquiv f hf N hM).apply_symm_apply e.inv)
  refine ⟨a, b, ?_, ?_⟩
  · apply (pullbackHom_bijective_of_isLineBundle f hf M hM).injective
    exact ((Scheme.Modules.pullback f).map_comp a b).trans
      ((congrArg₂ (fun c d ↦ c ≫ d) ha hb).trans
        (e.hom_inv_id.trans ((Scheme.Modules.pullback f).map_id M).symm))
  · apply (pullbackHom_bijective_of_isLineBundle f hf N hN).injective
    exact ((Scheme.Modules.pullback f).map_comp b a).trans
      ((congrArg₂ (fun c d ↦ c ≫ d) hb ha).trans
        (e.inv_hom_id.trans ((Scheme.Modules.pullback f).map_id N).symm))

theorem pullbackHom_bijective_of_proper_product
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left]
    (M : Y.left.Modules) {N : Y.left.Modules} (hN : LineBundle.Construction.IsLineBundle N) :
    Function.Bijective (fun q : M ⟶ N ↦
      (Scheme.Modules.pullback (CartesianMonoidalCategory.fst Y X).left).map q) :=
  pullbackHom_bijective_of_isLineBundle (CartesianMonoidalCategory.fst Y X).left
    (UniversalGlobalSections.Construction.isIso_properBaseChange_app Y X) M hN

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleDescent.Construction
