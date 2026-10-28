import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterPointedRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ClosedCarrierBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.MixedBoundaryCenterLift

/-! # Carrier Pointed Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CarrierPointedCenterLift.Construction

noncomputable section

/-! Native boundary-compatible carrier centers give actual ambient common-coordinate charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem global_closed_carrier_center_chart_on_native_normal_open
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I H : X.IdealSheafData) (hHI : H ≤ I)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) (I.comap H.subschemeι)
      (fun l => (D l).comap H.subschemeι))
    (U : X.affineOpens) (z : Γ(X, U)) (hHz : H.ideal U = Ideal.span {z})
    (w : β → Γ(X, U)) (hw : ∀ l, (D l).ideal U = Ideal.span {w l}) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    ∀ (N : Derivation ℂ Γ(X, U) Γ(X, U)), N z = 1 →
    ∀ p : PrimeSpectrum Γ(X, U), I.ideal U ≤ p.asIdeal →
      ∃ F : Finset β, Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart ℂ (.of Γ(X, U))
        (I.ideal U) w F p) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  intro N hNz p hp
  let Q := Γ(X, U) ⧸ H.ideal U
  let q : Γ(X, U) →ₐ[ℂ] Q := Ideal.Quotient.mkₐ ℂ (H.ideal U)
  let K := (I.ideal U).map q.toRingHom
  let j : Spec (.of Q) ⟶ H.subscheme := H.subschemeCover.f U
  let : IsOpenImmersion j := H.subschemeCover.openCover.map_prop U
  have hover : j ≫ H.subschemeι = Spec.map (CommRingCat.ofHom q.toRingHom) ≫ U.2.fromSpec :=
    ClosedCarrierBoundaryAtlas.Construction.subschemeChart_over_affine H U
  have hj : j ≫ (H.subschemeι ≫ f) = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure Q := by
    rw [← Category.assoc, hover]
    rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
    rfl
  have hK : (I.comap H.subschemeι).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K := by
    rw [← Scheme.IdealSheafData.comap_comp, hover]
    exact Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U q.toRingHom
  have hD (l : β) : ((D l).comap H.subschemeι).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {q (w l)}) := by
    rw [← Scheme.IdealSheafData.comap_comp, hover]
    have h := Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel (D l) U q.toRingHom
    rw [hw, Ideal.map_span, Set.image_singleton] at h
    exact h
  have hker : RingHom.ker q.toRingHom = Ideal.span {z} := by
    change RingHom.ker (Ideal.Quotient.mk (H.ideal U)) = Ideal.span {z}
    rw [Ideal.mk_ker, hHz]
  have hkI : RingHom.ker q.toRingHom ≤ I.ideal U := by
    change RingHom.ker (Ideal.Quotient.mk (H.ideal U)) ≤ I.ideal U
    rw [Ideal.mk_ker]
    exact hHI U
  have hqp : RingHom.ker q.toRingHom ≤ p.asIdeal := hkI.trans hp
  let P : PrimeSpectrum Q := ⟨p.asIdeal.map q.toRingHom,
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hqp⟩
  have hP : PrimeSpectrum.comap q.toRingHom P = p := by
    apply PrimeSpectrum.ext
    change (p.asIdeal.map q.toRingHom).comap q.toRingHom = p.asIdeal
    rw [Ideal.comap_map_of_surjective q.toRingHom Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hqp]
  have hKP : K ≤ P.asIdeal := Ideal.map_mono hp
  obtain ⟨F, C⟩ := A.exists_pointed_restriction (.of Q) j hj K (fun l => q (w l)) hK hD P hKP
  obtain ⟨C⟩ := C
  have hI : K.comap q.toRingHom = I.ideal U := by
    change ((I.ideal U).map q.toRingHom).comap q.toRingHom = I.ideal U
    rw [Ideal.comap_map_of_surjective q.toRingHom Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkI]
  have h := Blowups.Quotient.MixedBoundaryCenterLift.Construction.quotient_mixed_boundary_center_chart_lifts (.of Γ(X, U)) (.of Q) q
    Ideal.Quotient.mk_surjective z hker N hNz w K F p P hP C
  exact ⟨F, hI ▸ h⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CarrierPointedCenterLift.Construction
