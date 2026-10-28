import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterMap
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupChart

/-! # Blowup Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.BlowupFiber.Construction

noncomputable section

/-! An actual hypersurface retraction persists on the corresponding blowup charts. -/

universe u

variable {H R : Type u} [CommRing H] [CommRing R]
variable (K : Ideal H) (I : Ideal R) (φ : H →+* R) (r : R →+* H)
  (hsection : r.comp φ = RingHom.id H) (hKI : K.map φ ≤ I) (hIr : I.map r = K) (a : K)

include hsection hIr in
theorem retractedBlowup_chart_principal :
    I.map ((Blowup.Charts.Construction.blowupChartConstants K a).comp r) =
      Ideal.span {Blowup.Charts.Construction.blowupChartConstants K a (r (φ a.val))} := by
  rw [← Ideal.map_map, hIr, ExceptionalIdeal.Construction.blowupChart_extendedIdeal]
  rw [show r (φ a.val) = a.val from RingHom.congr_fun hsection a.val]

include hsection in
theorem retractedBlowup_chart_regular :
    IsRegular (Blowup.Charts.Construction.blowupChartConstants K a (r (φ a.val))) := by
  rw [show r (φ a.val) = a.val from RingHom.congr_fun hsection a.val]
  exact ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular K a

/-- Retraction of the ambient chart onto the actual chart of its hypersurface. -/
def retractedBlowupChartMap : Blowup.Charts.Construction.blowupChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) →+* Blowup.Charts.Construction.blowupChart K a :=
  ChartLift.Construction.blowupChartLift I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) ((Blowup.Charts.Construction.blowupChartConstants K a).comp r)
    (retractedBlowup_chart_principal K I φ r hsection hIr a)
    (retractedBlowup_chart_regular K φ r hsection a)

theorem retractedBlowupChartMap_constants (x : R) :
    retractedBlowupChartMap K I φ r hsection hKI hIr a
      (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) x) = Blowup.Charts.Construction.blowupChartConstants K a (r x) :=
  ChartLift.Construction.blowupChartLift_constants _ _ _ _ _ x

theorem retractedBlowupChartMap_subcenter :
    (retractedBlowupChartMap K I φ r hsection hKI hIr a).comp
      (Blowup.SubcenterMap.Construction.blowupSubcenterMap K I φ hKI a) = RingHom.id (Blowup.Charts.Construction.blowupChart K a) := by
  apply ChartLift.Construction.blowupChart_hom_ext K a (Blowup.Charts.Construction.blowupChartConstants K a) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular K a)
  · intro x
    rw [RingHom.comp_apply, Blowup.SubcenterMap.Construction.blowupSubcenterMap_constants, retractedBlowupChartMap_constants]
    rw [show r (φ x) = x from RingHom.congr_fun hsection x]
  · intro x
    rfl

variable (z : I) (hz : r z.val = 0)

include hz in
theorem retractedBlowupChartMap_normal :
    retractedBlowupChartMap K I φ r hsection hKI hIr a
      (ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z) = 0 := by
  let F := retractedBlowupChartMap K I φ r hsection hKI hIr a
  have he := congrArg F (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z)
  rw [map_mul F] at he
  have ha : F (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a)
      (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a).val) = Blowup.Charts.Construction.blowupChartConstants K a (r (φ a.val)) :=
    retractedBlowupChartMap_constants K I φ r hsection hKI hIr a (φ a.val)
  have hzF : F (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z.val) = 0 := by
    change retractedBlowupChartMap K I φ r hsection hKI hIr a
      (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z.val) = 0
    rw [retractedBlowupChartMap_constants, hz, map_zero]
  rw [ha, hzF] at he
  apply (retractedBlowup_chart_regular K φ r hsection a).left
  exact he.trans (mul_zero (Blowup.Charts.Construction.blowupChartConstants K a (r (φ a.val)))).symm

def retractedBlowupFiberMap :
    HypersurfaceBlowupChart.Construction.transformedHypersurfaceChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z →+* Blowup.Charts.Construction.blowupChart K a :=
  Ideal.Quotient.lift _ (retractedBlowupChartMap K I φ r hsection hKI hIr a) (by
    intro x hx
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hx
    rw [hs, map_mul, retractedBlowupChartMap_normal K I φ r hsection hKI hIr a z hz,
      zero_mul (retractedBlowupChartMap K I φ r hsection hKI hIr a s)])

def retractedBlowupFiberSection :
    Blowup.Charts.Construction.blowupChart K a →+* HypersurfaceBlowupChart.Construction.transformedHypersurfaceChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z :=
  (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})).comp
    (Blowup.SubcenterMap.Construction.blowupSubcenterMap K I φ hKI a)

theorem retractedBlowupFiberMap_section :
    (retractedBlowupFiberMap K I φ r hsection hKI hIr a z hz).comp
      (retractedBlowupFiberSection K I φ hKI a z) = RingHom.id (Blowup.Charts.Construction.blowupChart K a) :=
  retractedBlowupChartMap_subcenter K I φ r hsection hKI hIr a

variable (hquot : ∀ x : R, Ideal.Quotient.mk (Ideal.span {z.val}) (φ (r x)) =
  Ideal.Quotient.mk (Ideal.span {z.val}) x)
  (hc : IsRegular (Ideal.Quotient.mk
    (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})
    (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (φ a.val))))

include hquot hc in
theorem retractedBlowupFiberSection_map :
    (retractedBlowupFiberSection K I φ hKI a z).comp
      (retractedBlowupFiberMap K I φ r hsection hKI hIr a z hz) =
        RingHom.id (HypersurfaceBlowupChart.Construction.transformedHypersurfaceChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z) := by
  let q := Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z})
  have he : ((retractedBlowupFiberSection K I φ hKI a z).comp
      (retractedBlowupFiberMap K I φ r hsection hKI hIr a z hz)).comp q = q := by
    apply ChartLift.Construction.blowupChart_hom_ext I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a)
      (q.comp (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a))) hc
    · intro x
      change q (Blowup.SubcenterMap.Construction.blowupSubcenterMap K I φ hKI a
        (retractedBlowupChartMap K I φ r hsection hKI hIr a
          (Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) x))) = _
      rw [retractedBlowupChartMap_constants, Blowup.SubcenterMap.Construction.blowupSubcenterMap_constants]
      exact congrArg (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z) (hquot x)
    · intro x
      rfl
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun he x

/-- The quotient of the ambient blowup chart by its divided normal coordinate
is the actual hypersurface blowup chart, with its original section retained. -/
def retractedBlowupFiberEquiv :
    HypersurfaceBlowupChart.Construction.transformedHypersurfaceChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) z ≃+* Blowup.Charts.Construction.blowupChart K a :=
  RingEquiv.ofRingHom
    (retractedBlowupFiberMap K I φ r hsection hKI hIr a z hz)
    (retractedBlowupFiberSection K I φ hKI a z)
    (retractedBlowupFiberMap_section K I φ r hsection hKI hIr a z hz)
    (retractedBlowupFiberSection_map K I φ r hsection hKI hIr a z hz hquot hc)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.BlowupFiber.Construction
