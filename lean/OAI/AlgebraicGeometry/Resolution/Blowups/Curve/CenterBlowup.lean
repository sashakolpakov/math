import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.DifferentialCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalBlowup

/-! # Center Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterBlowup.Construction

noncomputable section

/-! The blowup of the intrinsic differential center on a smooth affine curve is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [IsNoetherianRing R]

/-- The actual blowup of a curve center with unit first differential ideal
is an isomorphism, using its original ideal and derivative-open cover. -/
theorem curve_center_blowup_isIso_of_first_differential_top
    (hd : ringKrullDim R ≤ 1) (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) :
    IsIso (ReesGrading.Construction.affineBlowupToSpec I) := by
  let s : Set R := (I : Set R) ∪ Set.range (fun t : Derivation k R R × I => t.1 t.2.val)
  have hs : Ideal.span s = ⊤ := by
    rw [Ideal.span_union, Ideal.span_eq]
    exact hI
  have hcover : (⨆ a : s, PrimeSpectrum.basicOpen a.val) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    simpa only [Subtype.range_val] using hs
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun a : s => PrimeSpectrum.basicOpen a.val) hcover
  rintro ⟨r, hr | ⟨⟨D, z⟩, rfl⟩⟩
  · have htop := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I r hr
    let a : I.map (algebraMap R (Localization.Away r)) := ⟨1, by rw [htop]; trivial⟩
    have hprincipal : I.map (algebraMap R (Localization.Away r)) = Ideal.span {a.val} := by
      change I.map (algebraMap R (Localization.Away r)) = Ideal.span {1}
      exact htop.trans Ideal.span_singleton_one.symm
    exact Locally.PrincipalBlowup.Construction.affineBlowup_basicOpen_isIso_of_local_principal I r a hprincipal isRegular_one
  · let A := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z.val
    let H := DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood D z.val
    let : Algebra.Smooth k H := DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood_smooth D z.val
    let : _root_.IsReduced H := Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k
    have hdH : ringKrullDim H ≤ 0 :=
      HypersurfaceDimension.Construction.differentialHypersurfaceNeighborhood_dimension_induction D z.val 0 (by simpa using hd)
    apply Locally.PrincipalBlowup.Construction.affineBlowup_basicOpen_isIso_of_localized
    exact Locally.PrincipalBlowup.Construction.zero_dimensional_hypersurface_center_blowup_isIso (algebraMap R A z.val)
      (HypersurfaceDimension.Construction.differentialHypersurfaceNeighborhood_equation_regular D z.val) hdH
      (I.map (algebraMap R A)) (Ideal.mem_map_of_mem _ z.property)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterBlowup.Construction
