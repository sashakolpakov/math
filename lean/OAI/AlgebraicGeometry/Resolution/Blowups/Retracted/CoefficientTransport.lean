import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.BlowupFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTransformIdeals

/-! # Coefficient Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientTransport.Construction

noncomputable section

/-! Coefficient transforms are the actual controlled transforms on the retracted hypersurface. -/

universe u

variable {H R : Type u} [CommRing H] [CommRing R]
variable (K : Ideal H) (I : Ideal R) (φ : H →+* R) (r : R →+* H)
  (hsection : r.comp φ = RingHom.id H) (hKI : K.map φ ≤ I) (hIr : I.map r = K) (a : K)
  (z : I) (hz : r z.val = 0)
  (hquot : ∀ x : R, Ideal.Quotient.mk (Ideal.span {z.val}) (φ (r x)) =
    Ideal.Quotient.mk (Ideal.span {z.val}) x)
  (hc : IsRegular (Ideal.Quotient.mk
    (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})
    (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (φ a.val))))
  (ρ : (R ⧸ Ideal.span {z.val}) →+* H)
  (hρ : ∀ x : R, ρ (Ideal.Quotient.mk (Ideal.span {z.val}) x) = r x)

include hρ in
theorem retractedBlowupFiberEquiv_base (x : R ⧸ Ideal.span {z.val}) :
    BlowupFiber.Construction.retractedBlowupFiberEquiv K I φ r hsection hKI hIr a z hz hquot hc
      (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z x) =
        Blowup.Charts.Construction.blowupChartConstants K a (ρ x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap_mk]
  change BlowupFiber.Construction.retractedBlowupChartMap K I φ r hsection hKI hIr a
    (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) x) = _
  rw [BlowupFiber.Construction.retractedBlowupChartMap_constants, hρ]

theorem retractedBlowupFiberEquiv_exceptional :
    BlowupFiber.Construction.retractedBlowupFiberEquiv K I φ r hsection hKI hIr a z hz hquot hc
      (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})
        (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (φ a.val))) =
          Blowup.Charts.Construction.blowupChartConstants K a a.val := by
  change BlowupFiber.Construction.retractedBlowupChartMap K I φ r hsection hKI hIr a
    (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (φ a.val)) = _
  rw [BlowupFiber.Construction.retractedBlowupChartMap_constants, show r (φ a.val) = a.val from RingHom.congr_fun hsection a.val]

include hρ in
/-- Under the actual fiber isomorphism, the divided coefficient ideal is
exactly the controlled transform on the hypersurface's own Rees chart.
This holds for every coefficient ideal and every control. -/
theorem retractedBlowupFiberEquiv_controlledIdeal
    (C : Ideal (R ⧸ Ideal.span {z.val})) (b : ℕ) :
    ((C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z)).colon
      (Ideal.span {(Ideal.Quotient.mk
        (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})
        (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (φ a.val))) ^ b})).map
          (BlowupFiber.Construction.retractedBlowupFiberEquiv K I φ r hsection hKI hIr a z hz hquot hc).toRingHom =
      ControlledTransform.Construction.blowupControlledTransform K (C.map ρ) b a := by
  let E := BlowupFiber.Construction.retractedBlowupFiberEquiv K I φ r hsection hKI hIr a z hz hquot hc
  have he : E.toRingHom.comp (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z) =
      (Blowup.Charts.Construction.blowupChartConstants K a).comp ρ := by
    apply RingHom.ext
    intro x
    exact retractedBlowupFiberEquiv_base K I φ r hsection hKI hIr a z hz hquot hc ρ hρ x
  have hmap : (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z)).map
      E.toRingHom = (C.map ρ).map (Blowup.Charts.Construction.blowupChartConstants K a) := by
    rw [Ideal.map_map, he, Ideal.map_map]
  let c := Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})
    (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (φ a.val))
  have hE : E c = Blowup.Charts.Construction.blowupChartConstants K a a.val :=
    retractedBlowupFiberEquiv_exceptional K I φ r hsection hKI hIr a z hz hquot hc
  have hcolon := PolynomialTransformIdeals.Construction.map_colon_principal_equiv
    (R := HypersurfaceBlowupChart.Construction.transformedHypersurfaceChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z)
    (S := Blowup.Charts.Construction.blowupChart K a) E
    (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z)) (c ^ b)
  rw [hmap, map_pow E, hE] at hcolon
  exact hcolon

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientTransport.Construction
