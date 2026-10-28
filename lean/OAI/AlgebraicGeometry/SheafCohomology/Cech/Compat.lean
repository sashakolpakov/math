/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/FlasqueCohomology.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Topology.Sheaves.Flasque
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing

/-! # Compat -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.Compat.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Option-free sheaf-cohomology compatibility

This is the narrow interface from AINTLIB's `FlasqueCohomology` needed by the
degree-one Cech comparison. The notation-level definitions are retained, but
the source's option-dependent flasque-acyclicity proof is not copied. Its two
consumed instances are instead derived from the existing project theorems
`injectiveSheaf_isFlasque` and `flasqueSheaf_H_succ_subsingleton`.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}}

/-- Regard a topological sheaf as a sheaf on the site of open subsets. -/
abbrev toSiteSheaf (F : Sheaf AddCommGrpCat.{u} X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  F

/-- Cohomology of an additive sheaf on a topological space. -/
abbrev H (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  CategoryTheory.Sheaf.H (toSiteSheaf F) n

/-- The map on cohomology induced by a morphism of additive sheaves. -/
abbrev H.map {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) (n : ℕ) :
    Compat.TopCat.Sheaf.H F n →+ Compat.TopCat.Sheaf.H G n :=
  CategoryTheory.Sheaf.H.map f n

/-- Degree-zero cohomology is equivalent to global sections. -/
abbrev H.equiv₀ (F : Sheaf AddCommGrpCat X) :
    Compat.TopCat.Sheaf.H F 0 ≃+ ↑((toSiteSheaf F).obj.obj (Opposite.op ⊤)) :=
  CategoryTheory.Sheaf.H.equiv₀ (toSiteSheaf F) Limits.isTerminalTop

namespace IsFlasque
open _root_.TopCat.Sheaf.IsFlasque

/-- Injective additive sheaves are flasque. -/
instance of_injective (I : Sheaf AddCommGrpCat.{u} X) [hI : Injective I] :
    IsFlasque I :=
  @AffineVanishing.Projective.injectiveSheaf_isFlasque
    X I hI

/-- Flasque additive sheaves have subsingleton positive-degree cohomology. -/
instance subsingleton_H {F : Sheaf AddCommGrpCat.{u} X} [hF : IsFlasque F]
    (n : ℕ) : Subsingleton (Compat.TopCat.Sheaf.H F (n + 1)) :=
  @AffineVanishing.Projective.flasqueSheaf_H_succ_subsingleton
    X F hF n

end IsFlasque

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.Compat.TopCat.Sheaf
