import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Hom Extension Local Rings -/

namespace OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings.LocalRings

noncomputable section

/-!
HomExtension: local rings of smooth schemes over factorial domains.
The integral-closure argument reuses the proved construction in
Proofs/SmoothNormal.lean, and the local-domain argument generalizes
Hodge/Algebraic/SmoothLocalDomain.lean from a field to a factorial domain.
No statement placeholders or unproved graph results are imported.
-/

open scoped TensorProduct

universe u v w

/-- A local ring integrally closed in a reduced Artinian extension forces
that extension to be a field: all idempotents lift and are trivial. -/
theorem isField_of_local_integrallyClosedIn_artinian
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsArtinianRing B] [IsReduced B] [Algebra A B]
    [IsIntegrallyClosedIn A B] : IsField B := by
  have hinj := (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn A B)).1
  let : Nontrivial B := hinj.nontrivial
  apply Foundations.Scheme.DomainFromGenericFiber.isField_of_artinian_reduced_idempotents_trivial B
  intro b hb
  have hbint : IsIntegral A b := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, hb.eq]
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hbint
  have haidem : IsIdempotentElem a := by
    change a * a = a
    apply hinj
    rw [map_mul, ha]
    exact hb
  rcases Foundations.Scheme.DomainFromGenericFiber.idempotent_eq_zero_or_one_of_local haidem with h0 | h1
  · left
    rw [← ha, h0, map_zero]
  · right
    rw [← ha, h1, map_one]

/-- Local localizations of etale algebras over normal domains are integrally
closed; no normality premise is imposed on the localized ring. -/
theorem isIntegrallyClosed_of_localization_of_etale
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (M : Submonoid S) [IsLocalization M A] : IsIntegrallyClosed A := by
  let K := FractionRing R
  let B := A ⊗[R] K
  let C := K ⊗[R] A
  let : Module.Flat S A := IsLocalization.flat A M
  let : Module.Flat R A := Module.Flat.trans R S A
  let : Algebra.FormallyUnramified S A := Algebra.FormallyUnramified.of_isLocalization M
  let : Algebra.FormallyUnramified R A := Algebra.FormallyUnramified.comp R S A
  let : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A M
  let : Algebra.EssFiniteType R A := Algebra.EssFiniteType.comp R S A
  let : Module.Finite K C := Algebra.FormallyUnramified.finite_of_free K C
  let : IsArtinianRing C := IsArtinianRing.of_finite K C
  let : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  let : IsArtinianRing B := (Algebra.TensorProduct.comm R K A).toRingEquiv.isArtinianRing
  let : IsReduced B := isReduced_of_injective
    (Algebra.TensorProduct.comm R A K).toRingHom (Algebra.TensorProduct.comm R A K).injective
  have hc : Function.Bijective (TensorProduct.toIntegralClosure R A K) :=
    TensorProduct.toIntegralClosure_bijective_of_tower
      (R := R) (S := S) (T := A) (B := K)
      TensorProduct.toIntegralClosure_bijective_of_smooth
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)
  let : IsIntegrallyClosedIn A B :=
    Foundations.Scheme.TensorIntegralClosure.isIntegrallyClosedIn_tensor_of_comparison_surjective hc.surjective
  let : Field B := (isField_of_local_integrallyClosedIn_artinian A B).toField
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn A B)).1
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn A B

/-- The actual prime localization of a smooth algebra over a field is normal. -/
theorem isIntegrallyClosed_localizationAtPrime_of_isSmoothAt
    (K : Type u) (S : Type v) [CommRing K] [IsDomain K] [UniqueFactorizationMonoid K] [CommRing S] [Algebra K S]
    [Algebra.FinitePresentation K S] (p : Ideal S) [p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨f, hfp, n, hPB, _, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  let B := Localization.Away f
  let A := Localization.AtPrime p
  let : Algebra P B := hPB
  let : Algebra.IsStandardEtale P B := hEtale
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsScalarTower S B A := IsLocalization.localization_isScalarTower_of_submonoid_le
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsLocalization (p.primeCompl.map (algebraMap S B)) A :=
    IsLocalization.isLocalization_of_submonoid_le B A (Submonoid.powers f) p.primeCompl hle
  let : Algebra P A := ((algebraMap B A).comp (algebraMap P B)).toAlgebra
  let : IsScalarTower P B A := IsScalarTower.of_algebraMap_eq' rfl
  exact isIntegrallyClosed_of_localization_of_etale P B A (p.primeCompl.map (algebraMap S B))

/-- Smoothness at a prime of a finitely presented algebra over a field makes
the corresponding local ring a domain. -/
theorem isDomain_localizationAtPrime_of_isSmoothAt
    (K : Type u) (S : Type v) [CommRing K] [IsDomain K] [UniqueFactorizationMonoid K] [CommRing S] [Algebra K S]
    [Algebra.FinitePresentation K S] (p : Ideal S) [p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsDomain (Localization.AtPrime p) := by
  obtain ⟨f, hfp, n, hPB, _, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  let B := Localization.Away f
  let A := Localization.AtPrime p
  let : Algebra P B := hPB
  let : Algebra.IsStandardEtale P B := hEtale
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsScalarTower S B A := IsLocalization.localization_isScalarTower_of_submonoid_le
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsLocalization (p.primeCompl.map (algebraMap S B)) A :=
    IsLocalization.isLocalization_of_submonoid_le
      B A (Submonoid.powers f) p.primeCompl hle
  let : Algebra P A := ((algebraMap B A).comp (algebraMap P B)).toAlgebra
  let : IsScalarTower P B A := IsScalarTower.of_algebraMap_eq' rfl
  exact Foundations.Scheme.EtaleLocalDomain.isDomain_of_localization_of_etale P B A
    (p.primeCompl.map (algebraMap S B))

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

/-- Smooth schemes over factorial domains have normal local domains. -/
theorem smooth_stalk_properties
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth f U hU
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : IsDomain (Localization.AtPrime p) :=
    isDomain_localizationAtPrime_of_isSmoothAt R Γ(X, U) p
  let : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_localizationAtPrime_of_isSmoothAt R Γ(X, U) p
  let e := IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x)
    (Localization.AtPrime p)
  exact ⟨e.injective.isDomain e.toRingHom, IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩

/-- Codimension-one stalks of smooth schemes over a DVR are DVRs. -/
theorem smooth_stalk_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Spec (.of R)) [Smooth f] (x : X) (hx : coheight x = 1) :
    letI := (smooth_stalk_properties f x).1
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let : IsDomain (X.presheaf.stalk x) := (smooth_stalk_properties f x).1
  let : IsIntegrallyClosed (X.presheaf.stalk x) := (smooth_stalk_properties f x).2
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  let : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun _ hp => hp.isMaximal_of_ne_bot ‹_›⟩
  let : IsDedekindDomain (X.presheaf.stalk x) := {}
  have hnf : ¬ IsField (X.presheaf.stalk x) := by
    intro h
    have he := ringKrullDim_stalk_eq_coheight x
    rw [ringKrullDim_eq_zero_of_isField h, hx] at he
    exact zero_ne_one he
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hnf).out 3 1).mp
    (show IsDedekindDomain (X.presheaf.stalk x) from inferInstance)

theorem integral_of_connected_of_stalk_domains
    (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] [ConnectedSpace X]
    (hlocal : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  let x : X := Classical.choice inferInstance
  have ho : IsOpen (irreducibleComponent x) :=
    Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains hlocal
      NoetherianSpace.finite_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents x)
  have hu : irreducibleComponent x = Set.univ :=
    (show IsClopen (irreducibleComponent x) from ⟨isClosed_irreducibleComponent, ho⟩).eq_univ
      ⟨x, mem_irreducibleComponent⟩
  have : IrreducibleSpace X := by
    apply (irreducibleSpace_def X).mpr
    change IsIrreducible (Set.univ : Set X)
    rw [← hu]
    exact isIrreducible_irreducibleComponent
  have : IsReduced X := Foundations.Scheme.LocalDomainComponents.isReduced_of_stalkDomains hlocal
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- The total space of a smooth connected-fiber proper scheme over a Noetherian
factorial domain is integral. -/
theorem integral_of_smooth_proper_connected
    {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Smooth f] [IsProper f] [GeometricallyConnected f] : IsIntegral X := by
  have : AlgebraicGeometry.IsNoetherian X := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    exact {}
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  exact integral_of_connected_of_stalk_domains X fun x => (smooth_stalk_properties f x).1

theorem exists_height_one_prime_containing
    {T : Type u} [CommRing T] [IsDomain T] [IsNoetherianRing T]
    (a : T) (ha : a ≠ 0) (haunit : ¬ IsUnit a) :
    ∃ p : Ideal T, p.IsPrime ∧ p.height = 1 ∧ a ∈ p := by
  have hproper : Ideal.span ({a} : Set T) ≠ ⊤ := by
    intro h
    exact haunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hproper
  have : p.IsPrime := hp.isPrime
  have hle : Ideal.span ({a} : Set T) ≤ p := hp.1.2
  refine ⟨p, inferInstance, le_antisymm ?_ ?_, hle (Ideal.subset_span (Set.mem_singleton a))⟩
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp
  · exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha)).trans (Ideal.height_mono hle)

theorem geometricallyIrreducible_of_smooth_proper_connected
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f] : GeometricallyIrreducible f := by
  constructor
  intro K _ e Z p q hp
  have : Smooth q := MorphismProperty.of_isPullback hp inferInstance
  have : IsProper q := MorphismProperty.of_isPullback hp inferInstance
  have : GeometricallyConnected q := MorphismProperty.of_isPullback hp inferInstance
  have : IsIntegral Z := integral_of_smooth_proper_connected q
  infer_instance

theorem fraction_isLocalization_away_uniformizer
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) : IsLocalization.Away π K := by
  have hle : Submonoid.powers π ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero)
  have hdiv : ∀ a ∈ nonZeroDivisors R, ∃ b ∈ Submonoid.powers π, a ∣ b := by
    intro a ha
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp ha) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π)
    (S := K) (nonZeroDivisors R) hle hdiv).mpr inferInstance

theorem fraction_inclusion_isOpenImmersion
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π K := fraction_isLocalization_away_uniformizer π hπ
  exact IsOpenImmersion.of_isLocalization π

theorem exists_codimension_one_in_special_fiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Spec (.of R)) [Smooth f] [Surjective f] :
    ∃ x : X, f x = IsLocalRing.closedPoint R ∧ coheight x = 1 := by
  obtain ⟨z, hz⟩ := f.surjective (IsLocalRing.closedPoint R)
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f V
  let := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth f V hV
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let pz := hV.primeIdealOf ⟨z, hzV⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let r : Γ(X, V) := algebraMap R Γ(X, V) π
  have hs : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) = hV.fromSpec ≫ f :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f V hV
  have hpz : PrimeSpectrum.comap (algebraMap R Γ(X, V)) pz = IsLocalRing.closedPoint R := by
    change Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) pz = _
    rw [hs]
    change f (hV.fromSpec pz) = _
    rw [hV.fromSpec_primeIdealOf]
    exact hz
  have hrpz : r ∈ pz.asIdeal := by
    change π ∈ (PrimeSpectrum.comap (algebraMap R Γ(X, V)) pz).asIdeal
    rw [hpz]
    exact hπ.not_isUnit
  have hr : r ≠ 0 := (map_ne_zero_iff (algebraMap R Γ(X, V))
    (FaithfulSMul.algebraMap_injective R Γ(X, V))).mpr hπ.ne_zero
  have hrunit : ¬ IsUnit r := by
    intro hu
    exact pz.2.ne_top (Ideal.eq_top_of_isUnit_mem pz.asIdeal hrpz hu)
  obtain ⟨p, hp, hheight, hrp⟩ := exists_height_one_prime_containing r hr hrunit
  let y : Spec Γ(X, V) := ⟨p, hp⟩
  have hybase : PrimeSpectrum.comap (algebraMap R Γ(X, V)) y = IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    apply le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.comap _ y).2.ne_top)
    rw [hπ.maximalIdeal_eq]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrp)
  refine ⟨hV.fromSpec y, ?_, ?_⟩
  · change (hV.fromSpec ≫ f) y = _
    rw [← hs]
    exact hybase
  · rw [coheight_eq_of_isOpenImmersion hV.fromSpec, ← idealHeight_eq_coheight]
    exact hheight

end

end OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings.LocalRings
