import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleScalarsApp
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

/-! # Linear Section Combinations -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LinearSectionCombinations.Construction

noncomputable section

/-! Finite linear combinations of actual line-bundle sections and
their regular coordinates after arbitrary pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators

universe u v
variable {X Y : Scheme.{u}} {M : X.Modules} {ι : Type v} [Fintype ι]

def sectionCombination (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (c : ι → Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M :=
  ∑ i, Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (c i) ≫ s i

def frameCoordinateAddHom (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso e] :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) →+ Γ(X, ⊤) where
  toFun := fun s => AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e s
  map_zero' := by
    change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (0 ≫ inv e) = 0
    rw [zero_comp, map_zero]
  map_add' s t := by
    change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X ((s + t) ≫ inv e) =
      AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (s ≫ inv e) + AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (t ≫ inv e)
    rw [Preadditive.add_comp, map_add]

theorem frameCoordinate_scalar_section (e s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso e]
    (c : Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) c ≫ s) =
      c * AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e s := by
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X
      (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinateEnd e s * Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) c) = _
  rw [map_mul, Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.structure_value, mul_comm]
  rfl

theorem frameCoordinate_sectionCombination (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) [IsIso e]
    (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (c : ι → Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e (sectionCombination s c) = ∑ i, c i * AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e (s i) := by
  change frameCoordinateAddHom e (∑ i, Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (c i) ≫ s i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact frameCoordinate_scalar_section e (s i) (c i)

theorem pullbackSection_combination (f : Y ⟶ X)
    (s : ι → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (c : ι → Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (sectionCombination s c) =
      sectionCombination (fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s i)) (fun i => f.appTop (c i)) := by
  simp only [sectionCombination, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_sum,
    Functor.map_comp, Preadditive.comp_sum, Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar]
  apply Finset.sum_congr rfl
  intro i _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Scheme.Modules.pullback f).map (s i))
      (Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars.scalar_naturality (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv (f.appTop (c i))).symm).trans
      (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LinearSectionCombinations.Construction
