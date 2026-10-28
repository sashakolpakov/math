import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothOpenDescent

/-! # Pointed Center Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedCenterSmooth.Construction

noncomputable section

/-! Actual generating neighborhoods detect smoothness of a native controlled closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowupBaseChangeReesChart_open (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U) →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] (a : (I.ideal U).map φ) :
    IsOpenImmersion (GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI U φ a) := by
  let : IsOpenImmersion (ReesMap.Construction.affineBlowupMap (I.ideal U) φ) := Affine.BlowupSmoothOpenDescent.Construction.affineBlowupMap_open_of_spec_open (I.ideal U) φ
  unfold GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart
  infer_instance

theorem globalBlowup_controlled_center_smooth_of_generating_neighborhoods
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ)
    (hperm : J ≤ I ^ b)
    (hlocal : ∀ x : X,
      ∃ (U : X.affineOpens) (S : CommRingCat) (_ : Algebra ℂ S) (_ : Algebra.Smooth ℂ S),
        letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
        ∃ (φ : Γ(X, U) →ₐ[ℂ] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) ∧
        ∃ q : PrimeSpectrum S, (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec) q = x ∧
        ∃ (κ : Type) (g : κ → (I.ideal U).map φ.toRingHom),
          Ideal.span (Set.range (fun a => (g a).val)) = (I.ideal U).map φ.toRingHom ∧
          ∀ a, Algebra.Smooth ℂ (Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ.toRingHom) (g a) ⧸
            ControlledTransform.Construction.blowupControlledTransform ((I.ideal U).map φ.toRingHom) ((J.ideal U).map φ.toRingHom) b (g a))) :
    Smooth ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).subschemeι ≫ (Data.Construction.globalBlowupToBase I hI ≫ f)) := by
  apply Global.PointedSmoothCenter.Construction.idealSheaf_complex_center_smooth_of_pointed_open_charts
  intro y
  obtain ⟨U, S, akS, hsS, φ, hopen, q, hq, κ, g, hgen, hsmooth⟩ := hlocal (Data.Construction.globalBlowupToBase I hI y)
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ S := akS
  let : Algebra.Smooth ℂ S := hsS
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hopen
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  have hφ : φ.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
  obtain ⟨a, p, hp⟩ := Global.EtaleBlowupCover.Construction.exists_generated_globalBlowup_baseChangeReesChart I hI U φ.toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hφ).1 g hgen y q hq.symm
  let R := Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ.toRingHom) (g a)
  let j := GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI U φ.toRingHom (g a)
  let : IsOpenImmersion j := globalBlowupBaseChangeReesChart_open I hI U φ.toRingHom (g a)
  refine ⟨.of R, inferInstance, j, inferInstance,
    PointedBounds.Construction.globalBlowupBaseChangeReesChart_complex_structure f I hI U φ (g a), p, hp,
    ControlledTransform.Construction.blowupControlledTransform ((I.ideal U).map φ.toRingHom) ((J.ideal U).map φ.toRingHom) b (g a),
    GlobalControlled.BaseChangeCharts.Construction.globalBlowupControlledIdeal_comap_baseChangeReesChart I J hI b hperm U φ.toRingHom (g a),
    hsmooth a⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedCenterSmooth.Construction
