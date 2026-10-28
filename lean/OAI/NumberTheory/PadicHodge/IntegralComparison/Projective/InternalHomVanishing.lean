import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTwist
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.CoproductVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Vanishing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentDimensions

/-! # Internal Hom Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomVanishing

noncomputable section

/-! The sheaf Hom terms of a sufficiently negative projective resolution
have no higher native Čech cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Vanishing OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem pole_isZero (j : σ) (m q : ℕ) :
    IsZero ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) := by
  have hcard : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨j⟩
  let : Subsingleton ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j (m : ℤ)).homology (q + 1)) :=
    AlgebraicGeometry.SheafCohomology.Projective.LaurentDimensions.MvPolynomial.coordinateHomogeneousLaurentPositiveHomology_subsingleton_of_degree_gt j (m : ℤ) q (by omega)
  let : Subsingleton ((Intrinsic.TwistResidueCoordinates.complex (R := R) j (m : ℤ)).homology (q + 1)) :=
    (HomologicalComplex.homologyMapIso (Intrinsic.TwistResidueCoordinates.laurentIso (R := R) j (m : ℤ))
      (q + 1)).toLinearEquiv.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton
    ((Intrinsic.TwistResidueCoordinates.complex (R := R) j (m : ℤ)).homology (q + 1))

theorem negative_isZero (j : σ) (a b : ℕ) (hba : b ≤ a) (q : ℕ) :
    IsZero ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)).obj
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b))) :=
  (pole_isZero j (a - b) q).of_iso ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)).mapIso
    (InternalHomTwist.negativeIso j a b hba))

theorem coproduct_isZero {I : Type} [Fintype I] (j : σ) (a : I → ℕ) (b : ℕ)
    (hba : ∀ i, b ≤ a i) (q : ℕ) :
    IsZero ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)).obj
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (∐ fun i : I => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (a i))
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b))) :=
  Contravariant.CoproductVanishing.isZero_image
    (SchemeInternalHom.functor (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) ⋙
      ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)) _
    (fun i => negative_isZero j (a i) b (hba i) q)

variable [IsNoetherianRing R]

theorem term_isZero
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (B b : ℕ) (hb : b ≤ B) (n q : ℕ) :
    IsZero ((ProjectiveResolution.Vanishing.cohomology (R := R) (σ := σ) (q + 1)).obj
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((NegativeResolution.complex M j B).X n)
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b))) := by
  let Q := NegativeResolution.presentation (NegativeResolution.state M j B n).module j B
  exact coproduct_isZero j Q.degree b (fun i => hb.trans (Q.degree_bound i)) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomVanishing
