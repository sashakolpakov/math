import OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionCoverEpi
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing

/-! # Positive Twist Section Generators -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistSectionGenerators

noncomputable section

/-! Every nonnegative projective hyperplane twist has actual finite global generators. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
namespace Dimension

universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def positiveTwistGeneratingSection (j : σ) (n : ℕ) (i : σ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Proj (MvPolynomial.homogeneousSubmodule σ R)) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n :=
  AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i) n ≫
    (UniversalPowers.Dimension.projectiveTwistUniversalPowerIso j n).inv

theorem positiveTwistGeneratingSection_cover (j : σ) (n : ℕ) :
    ∀ x : Proj (MvPolynomial.homogeneousSubmodule σ R),
      ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (positiveTwistGeneratingSection (R := R) j n i) := by
  intro x
  obtain ⟨i, hi⟩ := (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionCover (R := R) j).covers x
  let k : σ := i
  have hk : x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k) := hi
  have hp := AbelianModuli.HilbertConstruction.Power.Nonvanishing.sectionNonvanishing_le_tensorPowerSection _ n hk
  refine ⟨k, ?_⟩
  exact (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k) n)
    (UniversalPowers.Dimension.projectiveTwistUniversalPowerIso j n).symm).symm ▸ hp

theorem positiveTwistGeneratingSection_epi (j : σ) (n : ℕ) :
    Epi (Sigma.desc (positiveTwistGeneratingSection (R := R) j n)) :=
  SectionCoverEpi.module_epi_of_sections_cover _ _ (positiveTwistGeneratingSection_cover j n)

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistSectionGenerators
