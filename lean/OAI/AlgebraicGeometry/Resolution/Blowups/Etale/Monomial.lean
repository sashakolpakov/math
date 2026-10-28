import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface

/-! # Monomial -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Monomial.Construction

noncomputable section

/-! Coefficient-compatible étale coordinates and smooth centers for successive monomial steps. -/

open _root_.MvPolynomial

universe u

variable {σ R S : Type u} [CommRing R] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ R) S] [Algebra.Etale (MvPolynomial σ R) S]

omit [Algebra.Etale (MvPolynomial σ R) S] in
theorem etaleSubsetCoordinateMap_C (C : Finset σ) (i : C) (r : R) :
    MonomialStep.Construction.etaleSubsetCoordinateMap (R := R) (S := S) C i (MvPolynomial.C r) =
      Blowup.Charts.Construction.blowupChartConstants ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))
        ⟨algebraMap (MvPolynomial σ R) S (X i.val),
          Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩
        (algebraMap (MvPolynomial σ R) S (MvPolynomial.C r)) := by
  rw [MonomialStep.Construction.etaleSubsetCoordinateMap, RingHom.comp_apply, SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup_C,
    ChartLift.Construction.blowupChartMap_constants]

abbrev etaleSubsetCoordinateBaseAlgebra (C : Finset σ) (i : C) :
    Algebra R (MonomialStep.Construction.etaleSubsetCoordinateChart (R := R) (S := S) C i) :=
  (((Blowup.Charts.Construction.blowupChartConstants ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S))
      ⟨algebraMap (MvPolynomial σ R) S (X i.val),
        Ideal.mem_map_of_mem _ (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property⟩).comp
      (algebraMap (MvPolynomial σ R) S)).comp MvPolynomial.C).toAlgebra

abbrev etaleSubsetCoordinatePolynomialAlgebra (C : Finset σ) (i : C) :
    Algebra (MvPolynomial σ R) (MonomialStep.Construction.etaleSubsetCoordinateChart (R := R) (S := S) C i) :=
  (MonomialStep.Construction.etaleSubsetCoordinateMap (R := R) (S := S) C i).toAlgebra

attribute [local instance] etaleSubsetCoordinateBaseAlgebra etaleSubsetCoordinatePolynomialAlgebra

omit [Algebra.Etale (MvPolynomial σ R) S] in
/-- The new polynomial chart coordinates preserve the original coefficient base. -/
theorem etaleSubsetCoordinateChart_scalarTower (C : Finset σ) (i : C) :
    IsScalarTower R (MvPolynomial σ R) (MonomialStep.Construction.etaleSubsetCoordinateChart (R := R) (S := S) C i) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  exact (etaleSubsetCoordinateMap_C (S := S) C i r).symm

theorem etaleSubsetCoordinateChart_etale (C : Finset σ) (i : C) :
    Algebra.Etale (MvPolynomial σ R) (MonomialStep.Construction.etaleSubsetCoordinateChart (R := R) (S := S) C i) :=
  (RingHom.etale_algebraMap (R := MvPolynomial σ R)
    (S := MonomialStep.Construction.etaleSubsetCoordinateChart (R := R) (S := S) C i)).mp (MonomialStep.Construction.etaleSubsetCoordinateMap_etale C i)

variable [Finite σ] [Algebra R S] [IsScalarTower R (MvPolynomial σ R) S]

/-- The actual extended ideal defines a smooth center inside any compatible
étale ambient algebra. -/
theorem etaleSubsetCoordinateCenter_smooth (C : Finset σ) :
    Algebra.Smooth R (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)) := by
  let : Algebra.Smooth R (MvPolynomial σ R ⧸ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) :=
    Blowups.Smooth.SubsetCenter.Construction.subsetCoordinateCenter_smooth C
  exact Blowups.Smooth.TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Monomial.Construction
