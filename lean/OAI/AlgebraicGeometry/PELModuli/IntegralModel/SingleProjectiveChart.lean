import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! # Single Projective Chart -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SingleProjectiveChart

noncomputable section

/-! The single-chart Laurent coordinate map is an actual ring equivalence,
with the coefficient ring explicitly transported through Γ(Spec R). -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace PolarizationEmbedding

universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleProjectiveChartIntersection (i : σ) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) (fun _ : Fin 1 => ULift.up i) =
      SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
  change (∏ᶜ fun _ : Fin 1 => SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) = _
  rw [show (∏ᶜ fun _ : Fin 1 => SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) =
    ⨅ _ : Fin 1, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i from
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Preorder.isLimitIInf _)).to_eq]
  simp

def singleProjectiveChartRingEquiv (i : σ) :
    Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≃+*
      AddMonoidAlgebra Γ(Spec (.of R), ⊤)
        (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid
          (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun _ : Fin 1 => i))) :=
  ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.mapIso
    (eqToIso (singleProjectiveChartIntersection (R := R) i)).op).commRingCatIsoToRingEquiv.trans
      (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R)
        (fun _ : Fin 1 => ULift.up i))

theorem singleProjectiveChartRingEquiv_apply (i : σ)
    (r : Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) :
    singleProjectiveChartRingEquiv i r =
      SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R)
        (fun _ : Fin 1 => ULift.up i)
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R)
            (fun _ : Fin 1 => ULift.up i) 0)).op r) := rfl

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SingleProjectiveChart
