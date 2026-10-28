import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineCenterBlowup

/-! # Center Pointed Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame.Construction

noncomputable section

/-! Every point of a smooth closed center admits actual étale coordinates generating its ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem free_conormal_center_pointed_open_frame
    {k Q ι : Type u} [CommRing k] [CommRing Q] [Algebra k Q]
    (P : Algebra.Extension.{u} k Q) [Algebra.Smooth k P.Ring] [Algebra.FormallySmooth k Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι Q P.Cotangent) (hfg : P.ker.FG)
    (p : PrimeSpectrum P.Ring) (hIp : P.ker ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : P.Ring →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (v : ι → S) (D : ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        P.ker.map f.toRingHom = Ideal.span (Set.range v) := by
  classical
  obtain ⟨g, E, hgen, hE⟩ := ConormalBasisDerivations.Construction.exists_conormal_basis_generators_and_derivations P b
  let v : ι → P.Ring := fun i => (g i).val
  let G := Ideal.span (Set.range v)
  have hGI : G ≤ P.ker := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (g i).property)
  obtain ⟨r, hr, hlocal⟩ := ConormalBasisDerivations.Construction.exists_center_generator_principal_neighborhood P.ker G hfg hGI hgen.le
  let a := (JacobianDerivationFrame.Construction.derivationJacobian E v).det
  have hqa : algebraMap P.Ring Q a = 1 := by
    have hm : (algebraMap P.Ring Q).mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian E v) = 1 := by
      ext i j
      change algebraMap P.Ring Q (E i (g j).val) = (1 : Matrix ι ι Q) i j
      rw [hE, Matrix.one_apply]
    change algebraMap P.Ring Q (JacobianDerivationFrame.Construction.derivationJacobian E v).det = 1
    rw [RingHom.map_det, hm, Matrix.det_one]
  have haI : a - 1 ∈ P.ker := RingHom.mem_ker.mpr (by rw [map_sub, hqa, map_one, sub_self])
  have hrp : r ∉ p.asIdeal := ConormalBasisDerivations.Construction.generator_neighborhood_avoids_center_prime P.ker p.asIdeal hIp r hr
  have hap : a ∉ p.asIdeal := ConormalBasisDerivations.Construction.generator_neighborhood_avoids_center_prime P.ker p.asIdeal hIp a haI
  let A := Localization.Away r
  let : Algebra.Smooth P.Ring A := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k A := Algebra.Smooth.comp k P.Ring A
  let : Algebra.Etale P.Ring A := Algebra.Etale.of_isLocalizationAway r
  let fA : P.Ring →ₐ[k] A := IsScalarTower.toAlgHom k P.Ring A
  obtain ⟨pA, hpA⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hrp
  let EA : ι → Derivation k A A := fun i => Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) (E i)
  let vA : ι → A := fun i => fA (v i)
  have hdet : (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det = fA a := by
    have hm : JacobianDerivationFrame.Construction.derivationJacobian EA vA = fA.toRingHom.mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian E v) := by
      ext i j
      exact Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (E i) (v j)
    rw [hm, ← RingHom.map_det]
    rfl
  have hdetp : (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det ∉ pA.asIdeal := by
    rw [hdet]
    have he : pA.asIdeal.comap fA.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
    change a ∉ pA.asIdeal.comap fA.toRingHom
    rwa [he]
  let S := JacobianNeighborhood.Construction.derivationJacobianNeighborhood EA vA
  let : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  let fS : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f : P.Ring →ₐ[k] S := fS.comp fA
  obtain ⟨Q', hQ'⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det pA hdetp
  let w : ι → S := fun i => algebraMap A S (vA i)
  let F := JacobianDerivationFrame.Construction.normalizedJacobianFrame (JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation EA vA) w
  have hF : ∀ i j, F i (w j) = if i = j then 1 else 0 :=
    JacobianDerivationFrame.Construction.normalizedJacobianFrame_dual _ _ (JacobianNeighborhood.Construction.jacobianNeighborhood_jacobian_isUnit EA vA)
  let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det
  let : Algebra.Etale P.Ring S := Algebra.Etale.comp P.Ring A S
  refine ⟨.of S, inferInstance, inferInstance, f,
    ?_, Q', ?_, w, F, hF, ?_⟩
  · let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P.Ring A))) :=
        IsOpenImmersion.of_isLocalization r
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsOpenImmersion.of_isLocalization (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P.Ring A) ≫
      CommRingCat.ofHom (algebraMap A S)))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change (Q'.asIdeal.comap (algebraMap A S)).comap (algebraMap P.Ring A) = p.asIdeal
    have hQI : Q'.asIdeal.comap (algebraMap A S) = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hQ'
    rw [hQI]
    exact congrArg PrimeSpectrum.asIdeal hpA
  · change P.ker.map ((algebraMap A S).comp (algebraMap P.Ring A)) = _
    rw [← Ideal.map_map, hlocal, Ideal.map_map]
    dsimp only [G]
    rw [Ideal.map_span, ← Set.range_comp]
    rfl

theorem free_conormal_center_pointed_frame
    {k Q ι : Type u} [CommRing k] [CommRing Q] [Algebra k Q]
    (P : Algebra.Extension.{u} k Q) [Algebra.Smooth k P.Ring] [Algebra.FormallySmooth k Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι Q P.Cotangent) (hfg : P.ker.FG)
    (p : PrimeSpectrum P.Ring) (hIp : P.ker ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : P.Ring →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (v : ι → S) (D : ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        P.ker.map f.toRingHom = Ideal.span (Set.range v) := by
  obtain ⟨S, hSk, hSs, f, hf, rest⟩ := free_conormal_center_pointed_open_frame P b hfg p hIp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  exact ⟨S, hSk, hSs, f,
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance,
    rest⟩

theorem free_conormal_ideal_pointed_open_frame
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.FormallySmooth k (R ⧸ I)]
    [Module.Free (R ⧸ I) I.Cotangent] (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : ι → S) (D : ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        I.map f.toRingHom = Ideal.span (Set.range v) := by
  classical
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  let : Algebra.Smooth k P.Ring := inferInstanceAs (Algebra.Smooth k R)
  let e := Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I
  let : Module.Free (R ⧸ I) P.Cotangent := Module.Free.of_equiv e.symm
  let : Module.Finite (R ⧸ I) I.Cotangent := Blowups.Quotient.ConormalProjective.Construction.smooth_quotient_conormal_finite I
  let : Module.Finite (R ⧸ I) P.Cotangent := Module.Finite.equiv e.symm
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) P.Cotangent
  let : Fintype ι := Fintype.ofFinite ι
  have hfg : P.ker.FG := by
    change (RingHom.ker (Ideal.Quotient.mk I)).FG
    rw [Ideal.mk_ker]
    exact Ideal.fg_of_isNoetherianRing I
  have hp : P.ker ≤ p.asIdeal := by
    change RingHom.ker (Ideal.Quotient.mk I) ≤ p.asIdeal
    rwa [Ideal.mk_ker]
  obtain ⟨S, hSk, hSs, f, hf, q, hq, v, D, hD, hI⟩ :=
    free_conormal_center_pointed_open_frame P (Module.Free.chooseBasis (R ⧸ I) P.Cotangent) hfg p hp
  refine ⟨S, hSk, hSs, f, hf, q, hq, ι, inferInstance, inferInstance, v, D, hD, ?_⟩
  change (RingHom.ker (Ideal.Quotient.mk I)).map f.toRingHom = _ at hI
  rwa [Ideal.mk_ker] at hI

theorem free_conormal_ideal_pointed_frame
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.FormallySmooth k (R ⧸ I)]
    [Module.Free (R ⧸ I) I.Cotangent] (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : ι → S) (D : ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        I.map f.toRingHom = Ideal.span (Set.range v) := by
  obtain ⟨S, hSk, hSs, f, hf, rest⟩ := free_conormal_ideal_pointed_open_frame (k := k) I p hIp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  exact ⟨S, hSk, hSs, f,
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance,
    rest⟩

theorem smooth_center_pointed_open_frame
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : ι → S) (D : ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        I.map f.toRingHom = Ideal.span (Set.range v) := by
  classical
  obtain ⟨r, hr, hfree⟩ := ConormalLocalBasis.Construction.exists_smooth_center_conormal_free_neighborhood (k := k) I p.asIdeal hIp
  let A := Localization.Away r
  let : Algebra.Smooth R A := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k A := Algebra.Smooth.comp k R A
  let : Algebra.Smooth k (A ⧸ I.map (algebraMap R A)) := ExtendedQuotient.Construction.smooth_extended_quotient I
  let : Module.Free (A ⧸ I.map (algebraMap R A)) (I.map (algebraMap R A)).Cotangent := hfree
  let fA : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  obtain ⟨pA, hpA⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hr
  have hIpA : I.map (algebraMap R A) ≤ pA.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have he : pA.asIdeal.comap (algebraMap R A) = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
    rwa [he]
  obtain ⟨S, hSk, hSs, fS, hfS, q, hq, ι, hι, hdec, v, D, hD, hI⟩ :=
    free_conormal_ideal_pointed_open_frame (k := k) (I.map (algebraMap R A)) pA hIpA
  let f := fS.comp fA
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom fA.toRingHom)) := IsOpenImmersion.of_isLocalization r
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom fS.toRingHom)) := hfS
  have hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom fA.toRingHom ≫ CommRingCat.ofHom fS.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  refine ⟨S, hSk, hSs, f, hf, q, ?_, ι, hι, hdec, v, D, hD, ?_⟩
  · apply PrimeSpectrum.ext
    change (q.asIdeal.comap fS.toRingHom).comap fA.toRingHom = p.asIdeal
    have he : q.asIdeal.comap fS.toRingHom = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hpA
  · change I.map (fS.toRingHom.comp fA.toRingHom) = _
    rw [← Ideal.map_map]
    exact hI

theorem smooth_center_pointed_frame
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : ι → S) (D : ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        I.map f.toRingHom = Ideal.span (Set.range v) := by
  obtain ⟨S, hSk, hSs, f, hf, rest⟩ := smooth_center_pointed_open_frame (k := k) I p hIp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  exact ⟨S, hSk, hSs, f,
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance,
    rest⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame.Construction
