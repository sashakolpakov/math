import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Charts
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Isomorphic Blowup Chart Etale -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupChartEtale.Construction

noncomputable section

/-! Charts of an isomorphic actual blowup are étale over the original affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

theorem blowupChartConstants_spec_open_of_isIso (I : Ideal R) [IsIso (ReesGrading.Construction.affineBlowupToSpec I)]
    (a : I) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants I a))) := by
  rw [← Blowup.Charts.Construction.affineBlowup_chart_structureMap]
  infer_instance

/-- When the actual affine blowup is an isomorphism, every coefficient
map into a denominator chart is étale, including empty charts. -/
theorem blowupChartConstants_etale_of_isIso (I : Ideal R) [IsIso (ReesGrading.Construction.affineBlowupToSpec I)]
    (a : I) : (Blowup.Charts.Construction.blowupChartConstants I a).Etale := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants I a))) :=
    blowupChartConstants_spec_open_of_isIso I a
  have h : Etale (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants I a))) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupChartEtale.Construction
