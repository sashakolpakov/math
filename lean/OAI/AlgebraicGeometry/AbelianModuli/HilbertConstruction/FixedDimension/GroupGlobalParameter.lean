import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveComposition

/-! # Group Global Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupGlobalParameter

noncomputable section

/-! The concrete bounded group parameter over the fixed-dimension Hilbert base is quasi-projective over the original base and carries a projective universal proper commutative group of the specified smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

def fixedDimensionHilbertGroupParameter : Over S :=
  (Over.map (Parameters.fixedDimensionHilbertParameter S n P g).hom).obj
    (GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi)

def fixedDimensionHilbertGroupHilbertMap :
    fixedDimensionHilbertGroupParameter S n P g Pm Pi ⟶ Parameters.fixedDimensionHilbertParameter S n P g :=
  Over.homMk (GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom rfl

def fixedDimensionHilbertGroupParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertGroupParameter S n P g Pm Pi) :=
  (Parameters.fixedDimensionHilbertParameterQuasiProjectivePresentation S n P g).composition
    (GroupParameters.fixedDimensionHilbertGroupRelativeQuasiProjectivePresentation S n P g Pm Pi)

def fixedDimensionHilbertGroupUniversalProjectivePresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange
    (GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom

theorem fixedDimensionHilbertGroupParameter_geometric_family :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertGroupParameter S n P g Pm Pi)) ∧
    Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)) ∧
    IsProper (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom ∧
    SmoothOfRelativeDimension g (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom ∧
    (letI := GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi;
      IsCommMonObj (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)) :=
  ⟨⟨fixedDimensionHilbertGroupParameterQuasiProjectivePresentation S n P g Pm Pi⟩,
    ⟨fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi⟩,
    inferInstance, GroupParameters.fixedDimensionHilbertGroupUniversalFamily_dimension S n P g Pm Pi,
    GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj_comm S n P g Pm Pi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupGlobalParameter
