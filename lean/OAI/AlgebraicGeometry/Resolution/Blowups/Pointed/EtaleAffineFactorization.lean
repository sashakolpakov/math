import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.CenterRestriction

/-! # Etale Affine Factorization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization.Construction

noncomputable section

section

/-! Two actual pointed étale affine charts have a pointed common affine refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_pointed_global_etale_comparison
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (R S : CommRingCat)
    [Algebra ℂ R] [Algebra ℂ S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) [Etale j] [Etale l]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (hl : l ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hpq : j p = l q) :
    ∃ (T : CommRingCat) (_ : Algebra ℂ T) (φ : R →ₐ[ℂ] T) (ψ : S →ₐ[ℂ] T),
      φ.toRingHom.Etale ∧ ψ.toRingHom.Etale ∧
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
  · apply (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom φ)).mp
    rw [hφ]
    exact inferInstanceAs (Etale u)
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

/-! A pointed étale affine chart has an actual open refinement factoring through a native affine open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_pointed_etale_affine_factorization
    {X : Scheme} (R : CommRingCat) (q : Spec R ⟶ X) [Etale q] (p : PrimeSpectrum R) :
    ∃ (U : X.affineOpens) (S : CommRingCat) (φ : R →+* S) (ψ : Γ(X, U) →+* S),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ ψ.Etale ∧
      Spec.map (CommRingCat.ofHom φ) ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ U.2.fromSpec ∧
      ∃ P : PrimeSpectrum S, PrimeSpectrum.comap φ P = p := by
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := q p) trivial
  let V : X.affineOpens := ⟨U, hU⟩
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hrange : q p ∈ V.2.fromSpec.opensRange := by rw [V.2.opensRange_fromSpec]; exact hpU
  obtain ⟨r, hr⟩ := hrange
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback q V.2.fromSpec) p r hr.symm
  obtain ⟨S, a, ha, P, hP⟩ := Scheme.exists_Spec_apply_eq z
  let : IsOpenImmersion a := ha
  let u : Spec S ⟶ Spec R := a ≫ pullback.fst q V.2.fromSpec
  let v : Spec S ⟶ Spec Γ(X, V) := a ≫ pullback.snd q V.2.fromSpec
  let φ := (Spec.preimage u).hom
  let ψ := (Spec.preimage v).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = u := Spec.map_preimage u
  have hψ : Spec.map (CommRingCat.ofHom ψ) = v := Spec.map_preimage v
  refine ⟨V, S, φ, ψ, ?_, ?_, ?_, P, ?_⟩
  · rw [hφ]
    exact inferInstanceAs (IsOpenImmersion u)
  · apply (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom ψ)).mp
    rw [hψ]
    exact inferInstanceAs (Etale v)
  · rw [hφ, hψ]
    exact (Category.assoc _ _ _).trans ((congrArg (fun t => a ≫ t) pullback.condition).trans
      (Category.assoc _ _ _).symm)
  · change Spec.map (CommRingCat.ofHom φ) P = p
    rw [hφ]
    change pullback.fst q V.2.fromSpec (a P) = p
    exact (congrArg (pullback.fst q V.2.fromSpec) hP).trans hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleAffineFactorization.Construction
