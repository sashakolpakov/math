import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Global Open Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.GlobalOpenComparison.Construction

noncomputable section

section

/-! A pointed étale chart and an actual open chart have a common refinement open in the first chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_pointed_global_open_comparison
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (R S : CommRingCat)
    [Algebra ℂ R] [Algebra ℂ S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) [Etale j] [IsOpenImmersion l]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (hl : l ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hpq : j p = l q) :
    ∃ (T : CommRingCat) (_ : Algebra ℂ T) (φ : R →ₐ[ℂ] T) (ψ : S →ₐ[ℂ] T),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) ∧ ψ.toRingHom.Etale ∧
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ l ∧
      ∃ Q : PrimeSpectrum T, PrimeSpectrum.comap φ.toRingHom Q = p ∧ PrimeSpectrum.comap ψ.toRingHom Q = q := by
  obtain ⟨x, hxp, hxq⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback j l) p q hpq
  obtain ⟨T, a, ha, Q, hQ⟩ := Scheme.exists_Spec_apply_eq x
  let : IsOpenImmersion a := ha
  let u : Spec T ⟶ Spec R := a ≫ pullback.fst j l
  let v : Spec T ⟶ Spec S := a ≫ pullback.snd j l
  let φ : R →+* T := (Spec.preimage u).hom
  let ψ : S →+* T := (Spec.preimage v).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = u := Spec.map_preimage u
  have hψ : Spec.map (CommRingCat.ofHom ψ) = v := Spec.map_preimage v
  have hcomm : u ≫ j = v ≫ l := by
    dsimp only [u, v]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hbase : φ.comp (algebraMap ℂ R) = ψ.comp (algebraMap ℂ S) := by
    have he : CommRingCat.ofHom (φ.comp (algebraMap ℂ R)) =
        CommRingCat.ofHom (ψ.comp (algebraMap ℂ S)) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap ℂ R) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ S) ≫ CommRingCat.ofHom ψ)
      rw [Spec.map_comp, Spec.map_comp, hφ, hψ]
      change u ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R = v ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S
      rw [← hj, ← hl]
      simpa only [Category.assoc] using congrArg (fun m => m ≫ f) hcomm
    exact congrArg CommRingCat.Hom.hom he
  let : Algebra ℂ T := (φ.comp (algebraMap ℂ R)).toAlgebra
  let φₖ : R →ₐ[ℂ] T := { __ := φ, commutes' := fun _ => rfl }
  let ψₖ : S →ₐ[ℂ] T := { __ := ψ, commutes' := fun c => (RingHom.congr_fun hbase c).symm }
  refine ⟨T, inferInstance, φₖ, ψₖ, ?_, ?_, ?_, Q, ?_, ?_⟩
  · rw [hφ]
    exact inferInstanceAs (IsOpenImmersion u)
  · apply (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom ψ)).mp
    rw [hψ]
    exact inferInstanceAs (Etale v)
  · rw [hφ, hψ]
    exact hcomm
  · change Spec.map (CommRingCat.ofHom φ) Q = p
    rw [hφ]
    change pullback.fst j l (a Q) = p
    exact (congrArg (pullback.fst j l) hQ).trans hxp
  · change Spec.map (CommRingCat.ofHom ψ) Q = q
    rw [hψ]
    change pullback.snd j l (a Q) = q
    exact (congrArg (pullback.snd j l) hQ).trans hxq

end

/-! Two actual integral affine open charts have a pointed common integral noetherian affine open over the same complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_pointed_integral_affine_overlap
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (R S : CommRingCat)
    [Algebra ℂ R] [Algebra ℂ S] [IsDomain R] [IsNoetherianRing R]
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) [IsOpenImmersion j] [IsOpenImmersion l]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (hl : l ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hpq : j p = l q) :
    ∃ (T : CommRingCat) (_ : Algebra ℂ T), IsDomain T ∧ IsNoetherianRing T ∧
      ∃ (φ : R →ₐ[ℂ] T) (ψ : S →ₐ[ℂ] T),
        IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) ∧
        IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ∧
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ l ∧
        ∃ Q : PrimeSpectrum T, PrimeSpectrum.comap φ.toRingHom Q = p ∧ PrimeSpectrum.comap ψ.toRingHom Q = q := by
  obtain ⟨T, hT, φ, ψ, hφ, _, hcomm, Q, hQφ, hQψ⟩ :=
    exists_pointed_global_open_comparison f R S j l hj hl p q hpq
  let : Algebra ℂ T := hT
  let a := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let b := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let : IsOpenImmersion a := hφ
  let : IsOpenImmersion (b ≫ l) := hcomm ▸ inferInstanceAs (IsOpenImmersion (a ≫ j))
  let : IsOpenImmersion b := IsOpenImmersion.of_comp b l
  let : Nonempty (Spec T) := ⟨Q⟩
  let : IsIntegral (Spec T) := isIntegral_of_isOpenImmersion a
  let : IsLocallyNoetherian (Spec T) := LocallyOfFiniteType.isLocallyNoetherian a
  exact ⟨T, hT, (affine_isIntegral_iff T).mp inferInstance, isLocallyNoetherian_Spec.mp inferInstance,
    φ, ψ, hφ, inferInstanceAs (IsOpenImmersion b), hcomm, Q, hQφ, hQψ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.GlobalOpenComparison.Construction
