import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.Topology.Homotopy.TopCat.ToSSet
import Mathlib.Topology.Homotopy.Equiv

/-! # Homotopy -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

noncomputable section

/-!
# Homotopy invariance of genuine singular cohomology

A homotopy gives the usual chain homotopy in the opposite category of modules.
Passing back from the opposite category yields a cochain homotopy. Thus
homotopic continuous maps induce equal pullbacks on singular cohomology, and a
homotopy equivalence induces an isomorphism in every degree.
-/

open _root_.CategoryTheory Opposite

variable {R : Type} [Ring R]

/-- A simplicial homotopy induces a cochain homotopy on pullbacks. -/
def simplicialPullbackHomotopy (M : ModuleCat.{0} R)
    {K L : SSet.{0}} {f g : K ⟶ L} (H : SSet.Homotopy f g) :
    _root_.Homotopy (Functor.simplicialPullback M f) (Functor.simplicialPullback M g) :=
  (H.chainComplexMap (op M)).unop

/-- A continuous homotopy induces a cochain homotopy on singular pullbacks. -/
def singularPullbackHomotopy (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (Functor.singularPullback M f) (Functor.singularPullback M g) :=
  simplicialPullbackHomotopy M H.toSSet

/-- Homotopic continuous maps induce equal singular-cohomology pullbacks. -/
theorem singularCohomologyPullback_eq (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    Functor.singularCohomologyPullback M f n = Functor.singularCohomologyPullback M g n :=
  (singularPullbackHomotopy M H).homologyMap_eq n

/-- Proposition-valued version of homotopy invariance. -/
theorem singularCohomologyPullback_eq_of_homotopic (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : f.hom.Homotopic g.hom) (n : ℕ) :
    Functor.singularCohomologyPullback M f n = Functor.singularCohomologyPullback M g n := by
  obtain ⟨H⟩ := H
  exact singularCohomologyPullback_eq M H n

/-- A homotopy equivalence of spaces induces a homotopy equivalence of their
singular cochain complexes, contravariantly. -/
def singularCochainsHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (Basic.singularCochains M Y) (Basic.singularCochains M X) where
  hom := Functor.singularPullback M (TopCat.ofHom e.toFun)
  inv := Functor.singularPullback M (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
    simpa only [Functor.singularPullback_comp, Functor.singularPullback_id] using
      singularPullbackHomotopy M H
  homotopyInvHomId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
    simpa only [Functor.singularPullback_comp, Functor.singularPullback_id] using
      singularPullbackHomotopy M H

/-- A homotopy equivalence induces an isomorphism on genuine singular
cohomology in every degree. -/
def singularCohomologyIsoOfHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Basic.singularCohomology M Y n ≅ Basic.singularCohomology M X n :=
  (singularCochainsHomotopyEquiv M e).toHomologyIso n

end

end OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
