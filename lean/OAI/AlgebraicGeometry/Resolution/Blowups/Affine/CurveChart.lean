import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import Mathlib.RingTheory.Smooth.Basic

/-! # Curve Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveChart.Construction

noncomputable section

/-! Finite actual chart covers and smooth coefficient algebras after isomorphic curve blowups. -/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R]

/-- A Noetherian center has a finite family of actual elements generating
the ideal and hence a finite native Rees chart cover. -/
theorem exists_finite_blowup_generators [IsNoetherianRing R] (I : Ideal R) :
    ∃ s : Finset I, Ideal.span (Set.range (fun x : s => (x.val : I).val)) = I := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := I)
  have hrange : Set.range (fun x : s => (x.val : I)) = (s : Set I) := by
    ext x
    exact ⟨fun ⟨y, h⟩ => h ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  refine ⟨s, (Submodule.span_range_subtype_eq_top_iff I (fun x : s => (x.val : I).property)).mp ?_⟩
  rw [hrange]
  exact hs

variable (k : Type u) [CommRing k] [Algebra k R] [Algebra.Smooth k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Each actual chart remains smooth over the original coefficient ring. -/
theorem blowupChart_smooth_of_isIso (I : Ideal R) [IsIso (ReesGrading.Construction.affineBlowupToSpec I)] (a : I) :
    Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a) := by
  have hR : (algebraMap k R).Smooth := RingHom.smooth_algebraMap.mpr inferInstance
  have hC := ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp
    (IsomorphicBlowupChartEtale.Construction.blowupChartConstants_etale_of_isIso I a)).2
  have hS := RingHom.Smooth.comp hR hC
  exact RingHom.smooth_algebraMap.mp hS

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveChart.Construction
