import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian

/-! # Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology

noncomputable section

/-! The actual Ext-based Zariski cohomology functor of a module sheaf and its degree-zero section comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.AlgebraicGeometry

universe u

def zariskiFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙ CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n

instance zariskiFunctor_additive (X : Scheme.{u}) (n : ℕ) : (zariskiFunctor X n).Additive := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n
  change (F ⋙ G).Additive
  constructor
  intro M N f g
  change G.map (F.map (f + g)) = G.map (F.map f) + G.map (F.map g)
  rw [F.map_add, G.map_add]

abbrev H {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : Type u := (zariskiFunctor X n).obj M

def hZeroEquivGlobalSections {X : Scheme.{u}} (M : X.Modules) : ZariskiCohomology.H M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))

theorem hZeroEquivGlobalSections_naturality {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : ZariskiCohomology.H M 0) :
    f.app ⊤ (hZeroEquivGlobalSections M x) =
      hZeroEquivGlobalSections N ((zariskiFunctor X 0).map f x) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology
