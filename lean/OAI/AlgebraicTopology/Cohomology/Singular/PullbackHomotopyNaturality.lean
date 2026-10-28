import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy

/-! # Pullback Homotopy Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.PullbackHomotopyNaturality

noncomputable section

/-!
# Naturality of singular cochain homotopies under restriction

The actual singular prism homotopy commutes with a commuting square of
topological homotopies. In particular, a homotopy of pairs gives compatible
cochain homotopies on the ambient spaces and their subspaces.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite MonoidalCategory

variable {R : Type} [Ring R]

/-- The actual singular cochain homotopy is contravariantly natural under
a commuting square of topological homotopies. -/
theorem singularPullbackHomotopy_naturality (M : ModuleCat.{0} R)
    {X Y X' Y' : TopCat.{0}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (u : X' ⟶ X) (v : Y' ⟶ Y)
    (h : (u ▷ TopCat.I) ≫ H.h = H'.h ≫ v) (a b : ℕ) :
    (Singular.Homotopy.singularPullbackHomotopy M H).hom a b ≫ (Functor.singularPullback M u).f b =
      (Functor.singularPullback M v).f a ≫ (Singular.Homotopy.singularPullbackHomotopy M H').hom a b := by
  exact congrArg Quiver.Hom.unop
    (HomotopyNaturality.topologicalHomotopy_chain_naturality H H' u v h (op M) b a)

/-- Restricting the actual singular cochain homotopy of a pair agrees with
the actual cochain homotopy of the restricted homotopy. -/
theorem singularPullbackHomotopy_subspace_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (Singular.Homotopy.singularPullbackHomotopy M H).hom a b ≫
        (RelativeSequence.subspaceCochainRestriction M X A).f b =
      (RelativeSequence.subspaceCochainRestriction M Y B).f a ≫
        (Singular.Homotopy.singularPullbackHomotopy M (AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles.subspaceHomotopy hf hg H hH)).hom a b :=
  singularPullbackHomotopy_naturality M H (AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles.subspaceHomotopy hf hg H hH)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B)
    (AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles.subspaceHomotopy_square hf hg H hH) a b

end

end OAI.AlgebraicTopology.Cohomology.Singular.PullbackHomotopyNaturality
