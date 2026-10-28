import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateHypersurfaceMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Monomial
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Transformed Hypersurface Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransformedHypersurfaceCoordinates.Construction

noncomputable section

/-! The divided persistent hypersurface has actual étale polynomial coordinates. -/

universe u

variable {σ K S : Type u} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

omit [Algebra.Etale (MvPolynomial σ K) S] in
/-- Every non-denominator center coordinate becomes its actual Rees ratio. -/
theorem etaleSubsetCoordinateMap_center (C : Finset σ) (i h : C) (hhi : h.val ≠ i.val) :
    Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := K) (S := S) C i (MvPolynomial.X h.val) =
      ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
        (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C h) := by
  rw [Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap, RingHom.comp_apply,
    SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup_center C i h.val hhi h.property,
    Blowups.Etale.BlowupChart.Construction.blowupChartMap_ratio]

/-- The actual quotient by a divided coordinate on every other blowup chart
is étale over the remaining polynomial coordinates. -/
theorem etale_transformedHypersurface_exists_coordinates
    (C : Finset σ) (i h : C) (hhi : h.val ≠ i.val) :
    ∃ φ : MvPolynomial {j : σ // j ∉ ({h.val} : Finset σ)} K →+*
        (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateChart (R := K) (S := S) C i ⧸
          Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
            (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C h)}), φ.Etale := by
  let T := Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateChart (R := K) (S := S) C i
  let : Algebra (MvPolynomial σ K) T := Blowups.Etale.Monomial.Construction.etaleSubsetCoordinatePolynomialAlgebra C i
  let : Algebra.Etale (MvPolynomial σ K) T := Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateChart_etale C i
  obtain ⟨φ, hφ, _⟩ := Blowups.Etale.CoordinateHypersurfaceMap.Construction.etaleCoordinateHypersurface_exists_coordinates (R := K) (S := T) h.val
  have hex : ∃ φ : MvPolynomial {j : σ // j ∉ ({h.val} : Finset σ)} K →+*
      (T ⧸ Ideal.span {algebraMap (MvPolynomial σ K) T (MvPolynomial.X h.val)}), φ.Etale := ⟨φ, hφ⟩
  have he : algebraMap (MvPolynomial σ K) T (MvPolynomial.X h.val) =
      ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
        (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C h) :=
    etaleSubsetCoordinateMap_center C i h hhi
  rw [he] at hex
  exact hex

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransformedHypersurfaceCoordinates.Construction
