import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalTwistKernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Twist Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.TwistKernel

noncomputable section

/-! The kernel of restriction for the native projective twist is detected
by its canonical coefficients on the standard affine charts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [QuasiCompact f]
local instance c44ProjectiveTwistKernelMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory Y

theorem projectiveTwistedStructureMap_zero_iff (j : σ) (m : ℕ)
    (x : Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) :
    ((tensorRight (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).app ⊤
        ((Open.TwistKernel.PolarizationEmbedding.unitTensorLineIso (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)).inv.app ⊤ x) = 0 ↔
      ∀ i : σ, SheafCohomology.Projective.FrameSections.localTrivializationCoefficient _
        ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j m) x ∈
          f.ker.ideal ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i,
            SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩ := by
  apply GlobalTwistKernel.PolarizationEmbedding.globalTwistedStructureMap_zero_iff
  exact le_of_eq SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top.symm

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.TwistKernel
