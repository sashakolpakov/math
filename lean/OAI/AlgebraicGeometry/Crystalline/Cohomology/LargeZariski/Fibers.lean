import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Points
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mixed.SheafQuasiIsoLocality
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Fibers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Fibers.LargeZariskiFibers

noncomputable section

/-!
# Exact conservative Zariski fibers of the native large modules

Fibers are filtered colimits over the actual Zariski points. Exactness
and conservativity give detection of cohomology isomorphisms, with the
original module carriers and coefficient ring.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

def fiber (x : X) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) ⥤
    ModuleCat.{u + 1} R :=
  (Points.LargeZariskiPoints.point x).sheafFiber

instance finiteLimits (x : X) : PreservesFiniteLimits (fiber R X x) := by
  unfold fiber
  infer_instance

instance colimits (x : X) : PreservesColimitsOfSize.{0, 0} (fiber R X x) := by
  unfold fiber
  infer_instance

instance additive (x : X) : (fiber R X x).Additive :=
  Functor.additive_of_preserves_binary_products _

instance preservesHomology (x : X) : (fiber R X x).PreservesHomology := by
  unfold fiber
  infer_instance

def underlying (x : X) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) ⥤
    AddCommGrpCat.{u + 1} :=
  fiber R X x ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}

instance underlying_additive (x : X) : (underlying R X x).Additive := by
  unfold underlying
  infer_instance

instance underlying_preservesHomology (x : X) : (underlying R X x).PreservesHomology := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} R
  unfold underlying
  infer_instance

instance underlying_colimits (x : X) : PreservesColimitsOfSize.{0, 0} (underlying R X x) := by
  have : PreservesColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} R
  unfold underlying
  infer_instance

theorem quasiIsoAt_of_underlying
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) ℕ}
    (f : K ⟶ L) (n : ℕ)
    (h : ∀ x : X, QuasiIsoAt (((underlying R X x).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n) :
    QuasiIsoAt f n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply ((Points.LargeZariskiPoints.conservative (X := X)).jointlyReflectIsomorphisms
    (ModuleCat.{u + 1} R)).isIso_iff (HomologicalComplex.homologyMap f n) |>.mpr
  rintro ⟨_, ⟨x⟩⟩
  have : QuasiIsoAt (((underlying R X x).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n := h x
  have : IsIso ((underlying R X x).map (HomologicalComplex.homologyMap f n)) :=
    Mixed.SheafQuasiIsoLocality.MixedSheafQuasiIsoLocality.map_homologyMap_isIso (underlying R X x) f n
  have : IsIso ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
      ((fiber R X x).map (HomologicalComplex.homologyMap f n))) := this
  exact isIso_of_reflects_iso ((fiber R X x).map (HomologicalComplex.homologyMap f n))
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Fibers.LargeZariskiFibers
