import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform

/-! # Hypersurface Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupChart.Construction

noncomputable section

/-! Identifying the transformed coordinate hypersurface with its own Rees blowup chart. -/

universe u

variable {R : Type u} [CommRing R]

abbrev hypersurfaceCenterIdeal (I : Ideal R) (z : I) : Ideal (R ⧸ Ideal.span {z.val}) :=
  I.map (Ideal.Quotient.mk (Ideal.span {z.val}))

abbrev hypersurfaceCenterElement (I : Ideal R) (a z : I) : hypersurfaceCenterIdeal I z :=
  ⟨Ideal.Quotient.mk (Ideal.span {z.val}) a.val, Ideal.mem_map_of_mem _ a.property⟩

abbrev hypersurfaceBlowupChart (I : Ideal R) (a z : I) :=
  Blowup.Charts.Construction.blowupChart (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z)

abbrev transformedHypersurfaceChart (I : Ideal R) (a z : I) :=
  Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}

def ambientChartToHypersurfaceBlowup (I : Ideal R) (a z : I) :
    Blowup.Charts.Construction.blowupChart I a →+* hypersurfaceBlowupChart I a z :=
  ChartLift.Construction.blowupChartMap I (Ideal.Quotient.mk (Ideal.span {z.val})) a

theorem ambientChartToHypersurfaceBlowup_ratio (I : Ideal R) (a z : I) :
    ambientChartToHypersurfaceBlowup I a z (ExceptionalIdeal.Construction.blowupChartRatio I a z) = 0 := by
  let φ := Ideal.Quotient.mk (Ideal.span {z.val})
  let μ := ambientChartToHypersurfaceBlowup I a z
  apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular
    (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z)).left
  change Blowup.Charts.Construction.blowupChartConstants (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z)
      (φ a.val) * μ (ExceptionalIdeal.Construction.blowupChartRatio I a z) =
    Blowup.Charts.Construction.blowupChartConstants (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z)
      (φ a.val) * 0
  have hzero : φ z.val = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z.val)
  rw [← ChartLift.Construction.blowupChartMap_constants I φ a a.val]
  change μ (Blowup.Charts.Construction.blowupChartConstants I a a.val) * μ (ExceptionalIdeal.Construction.blowupChartRatio I a z) =
    μ (Blowup.Charts.Construction.blowupChartConstants I a a.val) * 0
  rw [← map_mul μ, ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio]
  have hb := ChartLift.Construction.blowupChartMap_constants I φ a z.val
  change μ (Blowup.Charts.Construction.blowupChartConstants I a z.val) = _ at hb
  rw [hb, hzero, map_zero, mul_zero (μ (Blowup.Charts.Construction.blowupChartConstants I a a.val))]

/-- The natural chart map kills the divided hypersurface equation. -/
def transformedHypersurfaceToBlowup (I : Ideal R) (a z : I) :
    transformedHypersurfaceChart I a z →+* hypersurfaceBlowupChart I a z :=
  Ideal.Quotient.lift _ (ambientChartToHypersurfaceBlowup I a z) (by
    intro r hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
    rw [hs, map_mul, ambientChartToHypersurfaceBlowup_ratio,
      zero_mul (ambientChartToHypersurfaceBlowup I a z s)])

theorem transformedHypersurfaceToBlowup_mk (I : Ideal R) (a z : I) (r : Blowup.Charts.Construction.blowupChart I a) :
    transformedHypersurfaceToBlowup I a z
      (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) r) =
      ambientChartToHypersurfaceBlowup I a z r := rfl

theorem transformedHypersurfaceToBlowup_base (I : Ideal R) (a z : I)
    (r : R ⧸ Ideal.span {z.val}) :
    transformedHypersurfaceToBlowup I a z (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z r) =
      Blowup.Charts.Construction.blowupChartConstants (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z) r := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap_mk, transformedHypersurfaceToBlowup_mk]
  exact ChartLift.Construction.blowupChartMap_constants I (Ideal.Quotient.mk (Ideal.span {z.val})) a r

theorem hypersurfaceCenter_extendedIdeal (I : Ideal R) (a z : I) :
    (hypersurfaceCenterIdeal I z).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z) =
      Ideal.span {HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z (hypersurfaceCenterElement I a z).val} := by
  change (I.map (Ideal.Quotient.mk (Ideal.span {z.val}))).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z) = _
  rw [Ideal.map_map]
  have he : (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z).comp (Ideal.Quotient.mk (Ideal.span {z.val})) =
      (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})).comp (Blowup.Charts.Construction.blowupChartConstants I a) := rfl
  rw [he, ← Ideal.map_map, ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.map_span, Set.image_singleton]
  rfl

/-- Regularity of the exceptional parameter gives a converse chart map. -/
def hypersurfaceBlowupToTransform (I : Ideal R) (a z : I)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    hypersurfaceBlowupChart I a z →+* transformedHypersurfaceChart I a z :=
  ChartLift.Construction.blowupChartLift (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z)
    (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z) (hypersurfaceCenter_extendedIdeal I a z) hc

theorem hypersurfaceBlowupToTransform_constants (I : Ideal R) (a z : I)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) (r : R ⧸ Ideal.span {z.val}) :
    hypersurfaceBlowupToTransform I a z hc
      (Blowup.Charts.Construction.blowupChartConstants (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z) r) =
      HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z r :=
  ChartLift.Construction.blowupChartLift_constants _ _ _ _ _ r

theorem transformedHypersurfaceToBlowup_toTransform (I : Ideal R) (a z : I)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    (transformedHypersurfaceToBlowup I a z).comp (hypersurfaceBlowupToTransform I a z hc) =
      RingHom.id (hypersurfaceBlowupChart I a z) := by
  apply ChartLift.Construction.blowupChart_hom_ext (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z)
    (Blowup.Charts.Construction.blowupChartConstants (hypersurfaceCenterIdeal I z) (hypersurfaceCenterElement I a z))
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular _ _)
  · intro r
    rw [RingHom.comp_apply, hypersurfaceBlowupToTransform_constants, transformedHypersurfaceToBlowup_base]
  · intro r
    rfl

theorem hypersurfaceBlowupToTransform_toBlowup (I : Ideal R) (a z : I)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    (hypersurfaceBlowupToTransform I a z hc).comp (transformedHypersurfaceToBlowup I a z) =
      RingHom.id (transformedHypersurfaceChart I a z) := by
  let π := Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
  have he : ((hypersurfaceBlowupToTransform I a z hc).comp
      (transformedHypersurfaceToBlowup I a z)).comp π = π := by
    apply ChartLift.Construction.blowupChart_hom_ext I a (π.comp (Blowup.Charts.Construction.blowupChartConstants I a)) hc
    · intro r
      change hypersurfaceBlowupToTransform I a z hc
        (transformedHypersurfaceToBlowup I a z (π (Blowup.Charts.Construction.blowupChartConstants I a r))) = _
      rw [transformedHypersurfaceToBlowup_mk, ambientChartToHypersurfaceBlowup,
        ChartLift.Construction.blowupChartMap_constants, hypersurfaceBlowupToTransform_constants,
        HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap_mk]
      rfl
    · intro r
      rfl
  apply RingHom.ext
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact congrArg (fun f : Blowup.Charts.Construction.blowupChart I a →+* transformedHypersurfaceChart I a z => f r) he

/-- The transformed hypersurface chart is the actual blowup chart of the
original hypersurface, whenever its exceptional parameter remains regular. -/
def hypersurfaceBlowupChartEquiv (I : Ideal R) (a z : I)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    transformedHypersurfaceChart I a z ≃+* hypersurfaceBlowupChart I a z :=
  RingEquiv.ofRingHom (transformedHypersurfaceToBlowup I a z) (hypersurfaceBlowupToTransform I a z hc)
    (transformedHypersurfaceToBlowup_toTransform I a z hc) (hypersurfaceBlowupToTransform_toBlowup I a z hc)

/-- Coordinate derivations supply the needed regularity over a Noetherian
rational algebra, giving the hypersurface blowup identification outright. -/
def noetherianHypersurfaceBlowupChartEquiv [IsNoetherianRing R] [Algebra ℚ R]
    (I : Ideal R) (a z : I) (D : Derivation ℤ R R) (ha : D a.val = 0) (hz : D z.val = 1) :
    transformedHypersurfaceChart I a z ≃+* hypersurfaceBlowupChart I a z :=
  hypersurfaceBlowupChartEquiv I a z (NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular I a z D ha hz)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceBlowupChart.Construction
