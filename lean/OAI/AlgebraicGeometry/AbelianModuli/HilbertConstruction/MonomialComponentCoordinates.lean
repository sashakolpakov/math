import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwoSectionMonomials
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentRatioLocalCoordinates

/-! # Monomial Component Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialComponentCoordinates

noncomputable section

/-! The ordinary component coordinate of a two-section monomial is the corresponding power of the original ratio. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M : X.Modules}

theorem sectionFrameOpen_le_power (s : Line.Bundles.structureModule X ⟶ M) (U : X.Opens)
    [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (d : ℕ) : U ≤ Ample.LineBundles.sectionNonvanishing (TensorPower.Maps.tensorPowerSection s d) :=
  le_sSup (Power.Nonvanishing.tensorPowerSection_pullback_isIso U.ι s d)

theorem twoSectionMonomial_componentCoordinate (s t : Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s) [IsIso (Ample.LineBundles.pullbackSection U.ι s)]
    (d i : ℕ) (hi : i ≤ d) :
    Section.ComponentRatios.sectionComponentRatio (TensorPower.Maps.tensorPowerSection s d) (TwoSectionMonomials.twoSectionMonomial s t d i hi) U
      (sectionFrameOpen_le_power s U d) = (Section.ComponentRatios.sectionComponentRatio s t U hU) ^ i := by
  have := Power.Nonvanishing.tensorPowerSection_pullback_isIso U.ι s d
  exact (ComponentRatioLocalCoordinates.componentRatio_localFrameCoordinate (TensorPower.Maps.tensorPowerSection s d)
    (TwoSectionMonomials.twoSectionMonomial s t d i hi) U (sectionFrameOpen_le_power s U d)).symm.trans
      ((congrArg U.topIso.hom (TwoSectionMonomials.twoSectionMonomial_localCoordinate U.ι s t d i hi)).trans
        (((U.topIso.hom).hom.map_pow _ i).trans
          (congrArg (fun r : Γ(X, U) => r ^ i) (ComponentRatioLocalCoordinates.componentRatio_localFrameCoordinate s t U hU))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialComponentCoordinates
