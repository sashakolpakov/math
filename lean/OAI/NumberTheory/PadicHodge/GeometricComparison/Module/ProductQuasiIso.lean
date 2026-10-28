import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Product Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.ProductQuasiIso.ModuleProductQuasiIso

noncomputable section

/-! Products of module complexes preserve objectwise quasi-isomorphisms.
This supplies the product step for the rows of the native Cech comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable (R : Type u) [CommRing R] (ι : Type)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}

local instance exactLimits : HasExactLimitsOfShape (Discrete ι) (ModuleCat.{max u v} R) :=
  HasExactLimitsOfShape.domain_of_functor (Discrete ι)
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

abbrev product : (Discrete ι ⥤ ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R := lim

local instance constAdditive :
    (Functor.const (Discrete ι) : ModuleCat.{max u v} R ⥤ Discrete ι ⥤ ModuleCat.{max u v} R).Additive where
  map_add := by intros; rfl

instance additive : (product.{u, v} R ι).Additive := by
  dsimp only [product]
  exact (constLimAdj (J := Discrete ι) (C := ModuleCat.{max u v} R)).right_adjoint_additive

instance preservesHomology : (product.{u, v} R ι).PreservesHomology := by
  dsimp only [product]
  infer_instance

variable {K L : CochainComplex (Discrete ι ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L)

theorem quasiIso (ha : ∀ i : Discrete ι,
    QuasiIso ((((evaluation (Discrete ι) (ModuleCat.{max u v} R)).obj i).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (((product.{u, v} R ι).mapHomologicalComplex (.up ℕ)).map a) := by
  let h : QuasiIso a := (HomologicalComplex.quasiIso_iff_evaluation a).mpr ha
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.ProductQuasiIso.ModuleProductQuasiIso
