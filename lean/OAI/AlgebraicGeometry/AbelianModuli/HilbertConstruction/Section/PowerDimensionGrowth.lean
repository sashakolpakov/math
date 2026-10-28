import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranscendentalPowerIndependence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialComponentCoordinates

/-! # Power Dimension Growth -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerDimensionGrowth

noncomputable section

/-! A transcendental ratio of two actual sections gives a linear lower bound on the dimensions of all finite tensor-power section spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem sectionPower_dimension_lowerBound (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    (s t : Line.Bundles.structureModule X ⟶ L.sheaf) (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s)
    [IsIso (Ample.LineBundles.pullbackSection U.ι s)]
    (hx : Transcendental K (show Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) U from
      ComponentRatios.sectionComponentRatio s t U hU)) (d : ℕ)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf)] :
    d + 1 ≤ Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf) := by
  have : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (TensorPower.PowerSheaf.tensorPowerModule L.sheaf d)) :=
    inferInstanceAs (Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf))
  let φ := Coefficient.SectionCoordinates.sectionCoordinateLinear p (TensorPower.Maps.tensorPowerSection s d) U (MonomialComponentCoordinates.sectionFrameOpen_le_power s U d)
  let v : Fin (d + 1) → (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf :=
    fun i => Global.Sections.moduleSectionHomEquiv (L.tensorPower d).sheaf
      (TwoSectionMonomials.twoSectionMonomial s t d i (Nat.le_of_lt_succ i.isLt))
  apply TranscendentalPowerIndependence.transcendental_powerValues_dimension_bound φ _ hx d v
  intro i
  exact (Coefficient.SectionCoordinates.sectionCoordinateLinear_value p (TensorPower.Maps.tensorPowerSection s d)
    (TwoSectionMonomials.twoSectionMonomial s t d i (Nat.le_of_lt_succ i.isLt)) U (MonomialComponentCoordinates.sectionFrameOpen_le_power s U d)).trans
      (MonomialComponentCoordinates.twoSectionMonomial_componentCoordinate s t U hU d i (Nat.le_of_lt_succ i.isLt))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerDimensionGrowth
