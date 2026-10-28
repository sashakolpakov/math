import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothOpenDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterFiniteFrameCover
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.OpenBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CenterRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PrincipalCenterSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalBlowup

/-! # Curve Center Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CurveCenterSmooth.Construction

noncomputable section

/-! A smooth curve coefficient center has a smooth entire ambient line-lifted blowup. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

theorem etaleLine_curve_center_blowup_smooth
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {H R : Type u} [CommRing H] [CommRing R] [Algebra k H] [Algebra k R]
    [Algebra H R] [IsScalarTower k H R] [Algebra H[X] R]
    [IsScalarTower H H[X] R] [Algebra.Etale H[X] R] [Algebra.Smooth k H]
    (K : Ideal H) (hdim : ringKrullDim H ≤ 1) (hK : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k K = ⊤) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  apply Affine.BlowupSmoothOpenDescent.Construction.affineBlowup_smooth_of_pointed_open_bases k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K)
  intro p
  obtain ⟨C, hp⟩ := Curve.CenterFiniteFrameCover.Construction.curve_center_frame_chart_at k hdim K hK (PrimeSpectrum.comap (algebraMap H R) p)
  change ∃ q : PrimeSpectrum C.carrier,
    PrimeSpectrum.comap C.map.toRingHom q = PrimeSpectrum.comap (algebraMap H R) p at hp
  obtain ⟨q, hq⟩ := hp
  obtain ⟨U, akU, aAU, aAPU, hkAU, hAPU, heU, g, hg, hz, hcoeff, Q, hQ, _⟩ :=
    OpenBaseChange.Construction.exists_etale_line_open_base_change C.map p q hq
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := hg
  have hcoef (h : H) : g (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (R := R) h) =
      Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (R := U) (C.map h) := by
    rw [NormalDerivation.Construction.etaleLineCoefficientMap_eq, NormalDerivation.Construction.etaleLineCoefficientMap_eq]
    exact hcoeff h
  have hI := CenterRefinement.Construction.etaleLineCenter_map_of_compatible_maps K C.map.toRingHom g.toRingHom hcoef hz
  refine ⟨U, akU, g, hg, Q, hQ, ?_⟩
  rw [hI]
  rcases C.center with hu | ⟨a, D, ha, hD⟩
  · rw [hu, RetractionStep.Construction.etaleLineCenter_eq, Ideal.map_top, top_sup_eq]
    let : Algebra.Smooth C.carrier C.carrier[X] := ⟨inferInstance, inferInstance⟩
    let : Algebra.Smooth k C.carrier[X] := Algebra.Smooth.comp k C.carrier C.carrier[X]
    let : Algebra.Smooth k U := Algebra.Smooth.comp k C.carrier[X] U
    let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal U)) :=
      PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal U) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k U))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance
  · rw [ha]
    exact PrincipalCenterSmooth.Construction.etaleLine_principal_center_blowup_smooth k a D hD

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CurveCenterSmooth.Construction
