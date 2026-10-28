import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback

/-! # Pushforward Sheaf Stalk -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PushforwardSheafStalk.Constructions

noncomputable section

/-! Pushforward along an embedding preserves the actual source stalk complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X Y : TopCat.{0}} (f : Y ⟶ X)

theorem sheafStalkPushforward_naturality {F G : TopCat.Sheaf (ModuleCat.{0} R) Y}
    (φ : F ⟶ G) (y : Y) :
    (stalkFunctor (ModuleCat.{0} R) (f y)).map
        (((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).map φ).hom) ≫
          stalkPushforward (ModuleCat.{0} R) f G.obj y =
      stalkPushforward (ModuleCat.{0} R) f F.obj y ≫
        (stalkFunctor (ModuleCat.{0} R) y).map φ.hom := by
  change (stalkFunctor (ModuleCat.{0} R) (f y)).map
      ((TopCat.Presheaf.pushforward (ModuleCat.{0} R) f).map φ.hom) ≫
        stalkPushforward (ModuleCat.{0} R) f G.obj y =
    stalkPushforward (ModuleCat.{0} R) f F.obj y ≫ (stalkFunctor (ModuleCat.{0} R) y).map φ.hom
  apply stalk_hom_ext
  intro U hy
  rw [← Category.assoc, stalkFunctor_map_germ, Category.assoc, stalkPushforward_germ,
    ← Category.assoc, stalkPushforward_germ, stalkFunctor_map_germ]
  rfl

def moduleSheafPushforwardComplex (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) :=
  ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def pushforwardSheafStalkComplexMap (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ)
    (y : Y) : AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (moduleSheafPushforwardComplex f K) (f y) ⟶
      AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K y where
  f n := stalkPushforward (ModuleCat.{0} R) f (K.X n).obj y
  comm' i j _ := (sheafStalkPushforward_naturality f (K.d i j) y).symm

def pushforwardSheafStalkComplexIso (hf : Topology.IsInducing f)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ) (y : Y) :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (moduleSheafPushforwardComplex f K) (f y) ≅
      AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex K y := by
  have hi : ∀ n, IsIso ((pushforwardSheafStalkComplexMap f K y).f n) := by
    intro n
    exact stalkPushforward.stalkPushforward_iso_of_isInducing (ModuleCat.{0} R) hf (K.X n).obj y
  have := HomologicalComplex.Hom.isIso_of_components (pushforwardSheafStalkComplexMap f K y)
  exact asIso (pushforwardSheafStalkComplexMap f K y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PushforwardSheafStalk.Constructions
