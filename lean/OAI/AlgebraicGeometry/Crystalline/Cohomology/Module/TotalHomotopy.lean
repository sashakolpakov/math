import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
import Mathlib.Algebra.Homology.HomotopyFiber

/-! # Total Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy.ModuleTotalHomotopy

noncomputable section

/-! Homotopic maps of first-quadrant module bicomplexes induce equal maps on total cohomology in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u v
variable {R : Type u} [CommRing R]

local instance totalExists (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

variable {K L : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}

theorem quasiIso_of_homotopyEquiv (e : HomotopyEquiv K L) :
    QuasiIso (HomologicalComplex₂.total.map e.hom (.up ℕ)) := by
  have columns (q : ℕ) : QuasiIso ((NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality.flipped e.hom).f q) := by
    exact inferInstanceAs (QuasiIso
      (((HomologicalComplex.eval (ModuleCat.{v} R) (.up ℕ) q).mapHomotopyEquiv e).hom))
  let : QuasiIso (HomologicalComplex₂.total.map (NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality.flipped e.hom) (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns _ columns
  apply (_root_.quasiIso_iff _).mpr
  intro n
  exact (NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality.quasiIsoAt_iff e.hom n).mp inferInstance

def totalHomology (i : ℕ) : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ) ⥤ ModuleCat.{v} R :=
  HomologicalComplex₂.totalFunctor (ModuleCat.{v} R) (.up ℕ) (.up ℕ) (.up ℕ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℕ) i

variable {f g : K ⟶ L} (h : Homotopy f g)

include h in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f (.up ℕ)) i =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map g (.up ℕ)) i := by
  let F := totalHomology.{u, v} (R := R) i
  let e : HomotopyEquiv L L.pathObject := pathObject.homotopyEquiv L (fun j => ⟨j + 1, rfl⟩)
  let := quasiIso_of_homotopyEquiv e
  let : IsIso (F.map (pathObject.ι L)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map e.hom (.up ℕ)) i))
  have projections : F.map (pathObject.π₀ L) = F.map (pathObject.π₁ L) := by
    apply (cancel_epi (F.map (pathObject.ι L))).mp
    rw [← F.map_comp, ← F.map_comp, pathObject.π₀_ι, pathObject.π₁_ι]
  change F.map f = F.map g
  calc
    F.map f = F.map (pathObject.lift f g h) ≫ F.map (pathObject.π₀ L) :=
      (congrArg F.map (pathObject.lift_π₀ f g h).symm).trans (F.map_comp _ _)
    _ = F.map (pathObject.lift f g h) ≫ F.map (pathObject.π₁ L) :=
      congrArg (F.map (pathObject.lift f g h) ≫ ·) projections
    _ = F.map g := (F.map_comp _ _).symm.trans (congrArg F.map (pathObject.lift_π₁ f g h))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy.ModuleTotalHomotopy
