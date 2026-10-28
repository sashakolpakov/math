import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface

/-! # Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart.Construction

noncomputable section

/-! Étale base change on the actual affine charts of a blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]

omit [Algebra R S] [Algebra.Etale R S] in
/-- Corresponding ratios are preserved by every actual coefficient chart map. -/
theorem blowupChartMap_ratio (I : Ideal R) (φ : R →+* S) (a b : I) :
    ChartLift.Construction.blowupChartMap I φ a (ExceptionalIdeal.Construction.blowupChartRatio I a b) =
      ExceptionalIdeal.Construction.blowupChartRatio (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩
        ⟨φ b.val, Ideal.mem_map_of_mem _ b.property⟩ := by
  let a' : I.map φ := ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩
  let b' : I.map φ := ⟨φ b.val, Ideal.mem_map_of_mem _ b.property⟩
  have h := congrArg (ChartLift.Construction.blowupChartMap I φ a) (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a b)
  rw [map_mul, ChartLift.Construction.blowupChartMap_constants, ChartLift.Construction.blowupChartMap_constants] at h
  have he : Blowup.Charts.Construction.blowupChartConstants (I.map φ) a' a'.val *
      ChartLift.Construction.blowupChartMap I φ a (ExceptionalIdeal.Construction.blowupChartRatio I a b) =
    Blowup.Charts.Construction.blowupChartConstants (I.map φ) a' a'.val * ExceptionalIdeal.Construction.blowupChartRatio (I.map φ) a' b' :=
    h.trans (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (I.map φ) a' b').symm
  exact (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular (I.map φ) a').left he

/-- The actual map between corresponding Rees charts is étale. -/
theorem blowupChartMap_scheme_etale (I : Ideal R) (a : I) :
    Etale (Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap I (algebraMap R S) a))) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (Blowup.FlatBaseChange.Construction.affineBlowupMap_chart_isPullback I (algebraMap R S) a).flip (Blowup.FlatBaseChange.Construction.affineBlowupMap_etale I)

theorem blowupChartMap_ringHom_etale (I : Ideal R) (a : I) :
    (ChartLift.Construction.blowupChartMap I (algebraMap R S) a).Etale :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mp (blowupChartMap_scheme_etale I a)

/-- The induced algebra structure on a target chart comes from the actual chart map. -/
abbrev etaleBlowupChartAlgebra (I : Ideal R) (a : I) :
    Algebra (Blowup.Charts.Construction.blowupChart I a)
      (Blowup.Charts.Construction.blowupChart (I.map (algebraMap R S)) ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩) :=
  (ChartLift.Construction.blowupChartMap I (algebraMap R S) a).toAlgebra

attribute [local instance] etaleBlowupChartAlgebra

theorem blowupChartMap_algebra_etale (I : Ideal R) (a : I) :
    Algebra.Etale (Blowup.Charts.Construction.blowupChart I a)
      (Blowup.Charts.Construction.blowupChart (I.map (algebraMap R S)) ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩) :=
  (RingHom.etale_algebraMap (R := Blowup.Charts.Construction.blowupChart I a)
    (S := Blowup.Charts.Construction.blowupChart (I.map (algebraMap R S)) ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩)).mp
      (blowupChartMap_ringHom_etale I a)

/-- Restriction to any closed subscheme of a source chart preserves this
étale algebra map, with the defining ideal actually extended to the target chart. -/
theorem blowupChartMap_quotient_etale (I : Ideal R) (a : I) (J : Ideal (Blowup.Charts.Construction.blowupChart I a)) :
    Algebra.Etale (Blowup.Charts.Construction.blowupChart I a ⧸ J)
      (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := S) I a ⧸
        J.map (@algebraMap (Blowup.Charts.Construction.blowupChart I a) (ChartFlatBaseChange.Construction.blowupBaseChangedChart (S := S) I a)
          inferInstance inferInstance inferInstance)) := by
  let : Algebra.Etale (Blowup.Charts.Construction.blowupChart I a)
      (Blowup.Charts.Construction.blowupChart (I.map (algebraMap R S)) ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩) :=
    blowupChartMap_algebra_etale I a
  exact Coordinate.Hypersurface.Construction.etale_quotient_of_etale J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart.Construction
