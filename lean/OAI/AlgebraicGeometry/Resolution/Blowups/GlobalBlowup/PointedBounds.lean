import OAI.AlgebraicGeometry.Resolution.Blowups.Global.EtaleBlowupCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedCoefficientBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality

/-! # Pointed Bounds -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedBounds.Construction

noncomputable section

/-! Actual generating neighborhoods and Rees base change turn local bounds into a global bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowupBaseChangeReesChart_complex_structure
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : X.affineOpens)
    {S : Type} [CommRing S] [Algebra ℂ S] :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    ∀ (φ : Γ(X, U) →ₐ[ℂ] S) (a : (I.ideal U).map φ.toRingHom),
    GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI U φ.toRingHom a ≫ (Data.Construction.globalBlowupToBase I hI ≫ f) =
      ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ.toRingHom) a) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  intro φ a
  rw [← Category.assoc, GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart_over, Category.assoc,
    ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((Blowup.Charts.Construction.blowupChartConstants ((I.ideal U).map φ.toRingHom) a).comp φ.toRingHom).comp
      (algebraMap ℂ Γ(X, U)))) = _
  apply congrArg (fun ψ : ℂ →+* Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ.toRingHom) a => Spec.map (CommRingCat.ofHom ψ))
  apply RingHom.ext
  intro c
  change Blowup.Charts.Construction.blowupChartConstants ((I.ideal U).map φ.toRingHom) a (φ (algebraMap ℂ Γ(X, U) c)) =
    Blowup.Charts.Construction.blowupChartConstants ((I.ideal U).map φ.toRingHom) a (algebraMap ℂ S c)
  rw [φ.commutes]

theorem globalBlowup_hasBound_of_generating_neighborhoods
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I J : X.IdealSheafData) (hI : I ≠ ⊥) (n m : ℕ)
    (hperm : J ≤ I ^ (n + 1)) [Smooth (Data.Construction.globalBlowupToBase I hI ≫ f)]
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n)
    (hlocal : ∀ x : X,
      ∃ (U : X.affineOpens) (S : CommRingCat) (_ : Algebra ℂ S) (_ : Algebra ℚ S) (_ : Algebra.Smooth ℂ S),
        letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
        ∃ (φ : Γ(X, U) →ₐ[ℂ] S), φ.toRingHom.Etale ∧
        ∃ q : PrimeSpectrum S, (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec) q = x ∧
        ∃ (κ : Type) (g : κ → (I.ideal U).map φ.toRingHom),
          Ideal.span (Set.range (fun a => (g a).val)) = (I.ideal U).map φ.toRingHom ∧
          ∀ a, ∃ C : Component.CenterChoice.Construction.ComponentCenterChoice ℂ (Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ.toRingHom) (g a))
            (ControlledTransform.Construction.blowupControlledTransform ((I.ideal U).map φ.toRingHom) ((J.ideal U).map φ.toRingHom) (n + 1) (g a)) n,
            C.HasBound m) : ∀ i, (B.choice i).HasBound m := by
  apply B.hasBound_of_pointed_etale_charts m
  intro y
  obtain ⟨U, S, akS, aqS, hsS, φ, hφ, q, hq, κ, g, hgen, hbound⟩ := hlocal (Data.Construction.globalBlowupToBase I hI y)
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ S := akS
  let : Algebra ℚ S := aqS
  let : Algebra.Smooth ℂ S := hsS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  obtain ⟨a, p, hp⟩ := Global.EtaleBlowupCover.Construction.exists_generated_globalBlowup_baseChangeReesChart I hI U φ.toRingHom
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hφ).1 g hgen y q hq.symm
  let R := Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ.toRingHom) (g a)
  let j := GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI U φ.toRingHom (g a)
  let : Etale j := GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart_etale I hI U φ.toRingHom hφ (g a)
  have hj : j ≫ (Data.Construction.globalBlowupToBase I hI ≫ f) = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R :=
    globalBlowupBaseChangeReesChart_complex_structure f I hI U φ (g a)
  let : Algebra.Smooth ℂ R := by
    have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hj ▸ inferInstanceAs (Smooth (j ≫ (Data.Construction.globalBlowupToBase I hI ≫ f)))
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap ℂ R))).mp hs)
  refine ⟨.of R, inferInstance, inferInstance, inferInstance, j, inferInstance, hj, p, hp,
    ControlledTransform.Construction.blowupControlledTransform ((I.ideal U).map φ.toRingHom) ((J.ideal U).map φ.toRingHom) (n + 1) (g a), ?_, hbound a⟩
  exact GlobalControlled.BaseChangeCharts.Construction.globalBlowupControlledIdeal_comap_baseChangeReesChart I J hI (n + 1) hperm U φ.toRingHom (g a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedBounds.Construction
