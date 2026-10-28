import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PolynomialRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.TwistKernel

/-! # Polynomial Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PolynomialKernel

noncomputable section

/-! The polynomial restriction map has the actual scheme-theoretic kernel:
its inverse polynomial section has local coefficients in the closed ideal. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [QuasiCompact f]
local instance c44ProjectivePolynomialKernelMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory Y

theorem nativeTwistSectionRestriction_zero_iff (j : σ) (m : ℕ)
    (x : (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) :
    PolynomialRestriction.PolarizationEmbedding.nativeTwistSectionRestriction f j m x = 0 ↔
      ∀ i : σ, SheafCohomology.Projective.FrameSections.localTrivializationCoefficient _
        ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j m) x ∈
          f.ker.ideal ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i,
            SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩ := by
  simp only [PolynomialRestriction.PolarizationEmbedding.nativeTwistSectionRestriction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff]
  exact TwistKernel.PolarizationEmbedding.projectiveTwistedStructureMap_zero_iff f j m x

variable [Fintype σ] [LinearOrder σ]

theorem nativePolynomialRestriction_zero_iff (j : σ) (m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ Γ(Spec (.of R), ⊤) m) :
    PolynomialRestriction.PolarizationEmbedding.nativePolynomialRestriction f j m p = 0 ↔
      ∀ i : σ, SheafCohomology.Projective.FrameSections.localTrivializationCoefficient _
        ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j m)
        ((SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m).symm p) ∈
          f.ker.ideal ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i,
            SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩ :=
  nativeTwistSectionRestriction_zero_iff f j m _

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PolynomialKernel
