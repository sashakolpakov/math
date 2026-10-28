import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Principal Open Factorization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenFactorization.Construction

noncomputable section

/-! Refine an actual affine open around a specified point by an original-ring principal open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_pointed_principal_open_factorization
    {k : Type u} [CommRing k] (R S : CommRingCat.{u}) [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (p : PrimeSpectrum R) (P : PrimeSpectrum S) (hP : PrimeSpectrum.comap f.toRingHom P = p) :
    ∃ r ∉ p.asIdeal, ∃ g : S →ₐ[k] Localization.Away r,
      IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) ∧
      g.comp f = IsScalarTower.toAlgHom k R (Localization.Away r) := by
  let j := Spec.map (CommRingCat.ofHom f.toRingHom)
  have hp : p ∈ j.opensRange := ⟨P, hP⟩
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp j.opensRange.isOpen p hp
  let A := Localization.Away r
  let l : Spec (.of A) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hsubset : Set.range l ⊆ Set.range j := by
    have hl : l.opensRange = PrimeSpectrum.basicOpen r :=
      Scheme.Hom.opensRange_localizationAway (R := R) r
    have hl' : Set.range l = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) :=
      congrArg (fun U : TopologicalSpace.Opens (Spec R) => (U : Set (Spec R))) hl
    rw [hl']
    exact hsub
  let a := IsOpenImmersion.lift j l hsubset
  have ha : a ≫ j = l := IsOpenImmersion.lift_fac j l hsubset
  let : IsOpenImmersion l := IsOpenImmersion.of_isLocalization r
  let : IsOpenImmersion (a ≫ j) := by rw [ha]; infer_instance
  let : IsOpenImmersion a := IsOpenImmersion.of_comp a j
  let φ : S →+* A := (Spec.preimage a).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = a := Spec.map_preimage a
  have hφf : φ.comp f.toRingHom = algebraMap R A := by
    have he : CommRingCat.ofHom (φ.comp f.toRingHom) = CommRingCat.ofHom (algebraMap R A) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom φ) = l
      rw [Spec.map_comp, hφ]
      exact ha
    exact congrArg CommRingCat.Hom.hom he
  let g : S →ₐ[k] A :=
    { __ := φ
      commutes' := by
        intro c
        calc
          φ (algebraMap k S c) = φ (f (algebraMap k R c)) := congrArg φ (f.commutes c).symm
          _ = algebraMap R A (algebraMap k R c) := RingHom.congr_fun hφf _
          _ = algebraMap k A c := (IsScalarTower.algebraMap_apply k R A c).symm }
  refine ⟨r, hr, g, ?_, ?_⟩
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))
    rw [hφ]
    infer_instance
  · ext x
    exact RingHom.congr_fun hφf x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenFactorization.Construction
