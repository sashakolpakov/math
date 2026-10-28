import OAI.AlgebraicGeometry.Comparison.Betti.Open.Image

/-! # Pushforward Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PushforwardStalk

noncomputable section

/-! The actual pushforward stalk map is natural and is invertible on embedded points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.TopCat.Presheaf

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

def sheafStalk (M : TopCat.{0}) (x : M) : ConstantSheafSections.ComplexSheaves M ⥤ ModuleCat.{0} ℂ :=
  TopCat.Sheaf.forget (ModuleCat.{0} ℂ) M ⋙ stalkFunctor (ModuleCat.{0} ℂ) x

instance sheafStalkAdditive (M : TopCat.{0}) (x : M) : (sheafStalk M x).Additive := by
  constructor
  intro F G φ ψ
  change (stalkFunctor (ModuleCat.{0} ℂ) x).map (φ.hom + ψ.hom) =
    (stalkFunctor (ModuleCat.{0} ℂ) x).map φ.hom + (stalkFunctor (ModuleCat.{0} ℂ) x).map ψ.hom
  exact (stalkFunctor (ModuleCat.{0} ℂ) x).map_add

variable {M N : TopCat.{0}} (f : M ⟶ N)

theorem pushforwardStalk_naturality {F G : M.Presheaf (ModuleCat.{0} ℂ)} (φ : F ⟶ G) (x : M) :
    (stalkFunctor (ModuleCat.{0} ℂ) (f x)).map ((pushforward (ModuleCat.{0} ℂ) f).map φ) ≫
        G.stalkPushforward (ModuleCat.{0} ℂ) f x =
      F.stalkPushforward (ModuleCat.{0} ℂ) f x ≫ (stalkFunctor (ModuleCat.{0} ℂ) x).map φ := by
  apply ((pushforward (ModuleCat.{0} ℂ) f).obj F).stalk_hom_ext
  intro U hx
  erw [← Category.assoc, stalkFunctor_map_germ, Category.assoc, stalkPushforward_germ,
    ← Category.assoc, stalkPushforward_germ, stalkFunctor_map_germ]
  rfl

def pushforwardStalkMap (x : M) : TopologicalSheafPullback.sheafDirectImage f ⋙ sheafStalk N (f x) ⟶ sheafStalk M x where
  app F := TopCat.Presheaf.stalkPushforward (ModuleCat.{0} ℂ) f F.obj x
  naturality _ _ φ := pushforwardStalk_naturality f φ.hom x

def pushforwardStalkIso (hf : Topology.IsInducing f) (x : M) :
    TopologicalSheafPullback.sheafDirectImage f ⋙ sheafStalk N (f x) ≅ sheafStalk M x := by
  have (F : ConstantSheafSections.ComplexSheaves M) : IsIso ((pushforwardStalkMap f x).app F) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing (ModuleCat.{0} ℂ) hf F.obj x
  exact NatIso.ofComponents (fun F => asIso ((pushforwardStalkMap f x).app F))
    (fun φ => (pushforwardStalkMap f x).naturality φ)

end

end OAI.AlgebraicGeometry.Comparison.Betti.PushforwardStalk
