import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.GlobalOpenComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealOverlapEquality
import OAI.AlgebraicGeometry.Resolution.Blowups.ExplicitLogarithmicDerivationPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CarrierOverlapData
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange

/-! # Normal Chart Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.NormalChartOverlap.Construction

noncomputable section

/-! Two actual logarithmic normal charts construct their native pointed tangent overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_tangent_overlap_of_modeled_normal_charts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J : X.IdealSheafData) {β : Type} (F : β → X.IdealSheafData)
    (R S : CommRingCat) [Algebra ℂ R] [Algebra ℂ S]
    [Algebra.Smooth ℂ R] [Algebra.Smooth ℂ S] [IsDomain R] [IsNoetherianRing R]
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) [IsOpenImmersion j] [IsOpenImmersion l]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (hl : l ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S)
    (I : Ideal R) (K : Ideal S) (hI : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel I) (hK : J.comap l = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (w : β → R) (v : β → S) (hw : ∀ i, (F i).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i}))
    (hv : ∀ i, (F i).comap l = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v i}))
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ R β w) (z : R) (t : S) (n : ℕ)
    (D : Derivation ℂ R R) (E : Derivation ℂ S S) (hDz : D z = 1) (hEt : E t = 1)
    (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ w) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ v)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ I n) (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ K n)
    [IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})).subscheme]
    [IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t})).subscheme]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hpq : j p = l q)
    (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ I n ≤ p.asIdeal) :
    ∃ A : TangentCarrierData.Construction.TangentCarrierOverlapData (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ I n))
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i}))
      (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S) (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ K n))
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t})) (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v i})) n,
      ∃ a : A.ambient, A.left a = p ∧ A.right a = q ∧ A.left ≫ j = A.right ≫ l := by
  obtain ⟨T, hT, hdom, hnoeth, φ, ψ, hφ, hψ, hcomm, Q, hQφ, hQψ⟩ :=
    Pointed.GlobalOpenComparison.Construction.exists_pointed_integral_affine_overlap f R S j l hj hl p q hpq
  let : Algebra ℂ T := hT
  let : IsDomain T := hdom
  let : IsNoetherianRing T := hnoeth
  let : Algebra ℚ T := ((algebraMap ℂ T).comp (algebraMap ℚ ℂ)).toAlgebra
  let a := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let b := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let : IsOpenImmersion a := hφ
  let : IsOpenImmersion b := hψ
  have hφe : φ.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
  have hψe : ψ.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom ψ.toRingHom)).mp inferInstance
  let : Algebra.Smooth ℂ T := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom ℂ φ hφe
  have hIK : I.map φ.toRingHom = K.map ψ.toRingHom :=
    Affine.IdealOverlapEquality.Construction.affine_ideal_maps_eq_of_common_diagram J R S T j l φ.toRingHom ψ.toRingHom hcomm I K hI hK
  have hboundary : ∀ i, Ideal.span {φ (w i)} = Ideal.span {ψ (v i)} :=
    Affine.IdealOverlapEquality.Construction.affine_boundary_spans_eq_of_common_diagram F R S T j l φ.toRingHom ψ.toRingHom hcomm w v hw hv
  let D0 := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ.toRingHom hφe φ.commutes D
  let E0 := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ ψ.toRingHom hψe ψ.commutes E
  have hD0 : D0 (φ z) = 1 := by
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ.toRingHom hφe φ.commutes D (φ.toRingHom z) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hDz, map_one]
  have hE0 : E0 (ψ t) = 1 := by
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ ψ.toRingHom hψe ψ.commutes E (ψ.toRingHom t) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hEt, map_one]
  have hDlog : D0 ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ (fun i => φ (w i)) :=
    ExplicitLogarithmicDerivationPullback.Construction.extendEtaleRingDerivationHom_relative_logarithmic φ hφe w D hD
  have hElog : E0 ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ (fun i => φ (w i)) :=
    ExplicitLogarithmicDerivationPullback.Construction.extendEtaleRingDerivationHom_logarithmic_of_ideal_eq ψ hψe v (fun i => φ (w i))
      (fun i => (hboundary i).symm) E hE
  have hz0 : φ z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.map φ.toRingHom) n := by
    rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map ℂ φ hφe]
    exact Ideal.mem_map_of_mem _ hz
  have ht0 : ψ t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.map φ.toRingHom) n := by
    rw [hIK, ← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map ℂ ψ hψe]
    exact Ideal.mem_map_of_mem _ ht
  have hQ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.map φ.toRingHom) n ≤ Q.asIdeal := by
    rw [← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map ℂ φ hφe, Ideal.map_le_iff_le_comap]
    have he : Q.asIdeal.comap φ.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hQφ
    rw [he]
    exact hp
  obtain ⟨B, u, hu, hu', hover⟩ := CarrierOverlapData.Construction.exists_modeled_carrier_overlap_data T (fun i => φ (w i))
    (M.baseChange φ hφe) (I.map φ.toRingHom) (φ z) (ψ t) n hz0 ht0 D0 E0 hD0 hE0 hDlog hElog Q hQ
    (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ I n))
    (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i}))
    (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S) (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ K n))
    (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t})) (fun i => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v i}))
    a b (Affine.IdealOverlapEquality.Construction.complexSpecStructure_specMap_algHom R T φ) (Affine.IdealOverlapEquality.Construction.complexSpecStructure_specMap_algHom S T ψ)
    (by rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Coefficient.ComponentBaseChange.Construction.smooth_relativeHomogenizedIdeal_map ℂ φ hφe])
    (by rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Coefficient.ComponentBaseChange.Construction.smooth_relativeHomogenizedIdeal_map ℂ ψ hψe, hIK])
    (by rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton])
    (by rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton])
    (by intro i; rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton])
    (by intro i; rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton, hboundary i])
  exact ⟨B, u, hu.trans hQφ, hu'.trans hQψ, hover j l hcomm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.NormalChartOverlap.Construction
