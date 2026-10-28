import OAI.ArithmeticGeometry.Models.SpreadingOut.Fg
import OAI.ArithmeticGeometry.Models.SpreadingOut.Affine
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothShrink
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Locus

/-! # Generic Smoothness -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GenericSmoothness.Construction

noncomputable section

/-! Smoothness at points of an affine scheme lying above the generic point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors

universe u

/-- A prime above the generic point has a local ring that is a localization
of the generic fiber. Formal smoothness of that fiber therefore implies
formal smoothness at the original prime. -/
theorem isSmoothAt_of_formallySmooth_generic_fiber
    {R K S : Type u} [CommRing R] [IsDomain R] [Field K] [CommRing S]
    [Algebra R K] [IsFractionRing R K] [Algebra R S]
    [Algebra.FormallySmooth K (K ⊗[R] S)]
    (p : Ideal S) [p.IsPrime]
    (hp : Ideal.comap (algebraMap R S) p = ⊥) : Algebra.IsSmoothAt R p := by
  let G := K ⊗[R] S
  let Sp := Localization.AtPrime p
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  have hM : M ≤ p.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    intro h
    have hz : r ∈ Ideal.comap (algebraMap R S) p := h
    rw [hp] at hz
    exact nonZeroDivisors.ne_zero hr hz
  let : Algebra S G := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization M G := inferInstance
  let : Algebra G Sp :=
    IsLocalization.localizationAlgebraOfSubmonoidLe G Sp M p.primeCompl hM
  have : IsScalarTower S G Sp :=
    IsLocalization.localization_isScalarTower_of_submonoid_le G Sp M p.primeCompl hM
  have : IsScalarTower R G Sp := IsScalarTower.to₁₃₄ R S G Sp
  let : Algebra K Sp :=
    ((algebraMap G Sp).comp (algebraMap K G)).toAlgebra
  have : IsScalarTower K G Sp := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R K Sp := IsScalarTower.to₁₂₄ R K G Sp
  have : IsLocalization (p.primeCompl.map (algebraMap S G)) Sp :=
    IsLocalization.isLocalization_of_submonoid_le G Sp M p.primeCompl hM
  have : Algebra.FormallySmooth G Sp :=
    Algebra.FormallySmooth.of_isLocalization (p.primeCompl.map (algebraMap S G))
  have : Algebra.FormallySmooth K Sp := Algebra.FormallySmooth.comp K G Sp
  have : Algebra.FormallySmooth R K :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors R)
  exact Algebra.FormallySmooth.comp R K Sp

/-- Algebraic smoothness at a prime places the corresponding point in the
scheme-theoretic smooth locus. -/
theorem affine_mem_smoothLocus_of_isSmoothAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (p : PrimeSpectrum S) [Algebra.IsSmoothAt R p.asIdeal] :
    (p : Spec (CommRingCat.of S)) ∈ (Affine.Construction.affineOver R S).hom.smoothLocus := by
  obtain ⟨s, hs, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R p.asIdeal
  let L := Localization.Away s
  let := hsm
  let v := Spec.map (CommRingCat.ofHom (algebraMap S L))
  let f := (Affine.Construction.affineOver R S).hom
  have : Smooth (v ≫ f) := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap S L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    rw [← Spec.map_comp]
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change RingHom.Smooth ((algebraMap S L).comp (algebraMap R S))
    rw [← IsScalarTower.algebraMap_eq R S L]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have hpr : p ∈ (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) := hs
  rw [← PrimeSpectrum.localization_away_comap_range L s] at hpr
  obtain ⟨q, hq⟩ := hpr
  have hq' : v q = (p : Spec (CommRingCat.of S)) := hq
  have hqsm : (q : Spec (CommRingCat.of L)) ∈ v ⁻¹ᵁ f.smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    trivial
  change v q ∈ f.smoothLocus at hqsm
  rw [hq'] at hqsm
  exact hqsm

/-- Smoothness of an affine generic fiber gives smoothness of its tensor algebra. -/
theorem smooth_generic_tensor_of_smooth_pullback
    (R K S : Type u) [CommRing R] [CommRing K] [CommRing S]
    [Algebra R K] [Algebra R S]
    [Smooth (pullback.snd (Affine.Construction.affineOver R S).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Algebra.Smooth K (K ⊗[R] S) := by
  let e := Affine.Construction.baseChangeAffineIso R K S
  have : IsIso e.inv.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of K))).map e.inv))
  have hs : Smooth (e.inv.left ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (Affine.Construction.affineOver R S)).hom) := by
    change Smooth (e.inv.left ≫ pullback.snd (Affine.Construction.affineOver R S).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    infer_instance
  rw [e.inv.w] at hs
  exact RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

theorem affine_generic_point_mem_smoothLocus
    (R K S : Type u) [CommRing R] [IsDomain R] [Field K] [CommRing S]
    [Algebra R K] [IsFractionRing R K] [Algebra R S]
    [Algebra.FinitePresentation R S]
    [Smooth (pullback.snd (Affine.Construction.affineOver R S).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (p : PrimeSpectrum S) (hp : Ideal.comap (algebraMap R S) p.asIdeal = ⊥) :
    (p : Spec (CommRingCat.of S)) ∈ (Affine.Construction.affineOver R S).hom.smoothLocus := by
  have := smooth_generic_tensor_of_smooth_pullback R K S
  have := isSmoothAt_of_formallySmooth_generic_fiber (K := K) p.asIdeal hp
  exact affine_mem_smoothLocus_of_isSmoothAt R S p

/-- Smoothness of the generic fiber implies smoothness at every point lying
above the generic point of an integral affine base. -/
theorem generic_point_mem_smoothLocus
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (x : X) (hx : f x = (show PrimeSpectrum R from ⊥)) : x ∈ f.smoothLocus := by
  let V := X.affineOpenCover
  let i := V.idx x
  obtain ⟨y, hy⟩ := V.covers x
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hsm : Smooth (pullback.snd (V.f i ≫ f) g) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd f g (V.f i)]
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.f i ≫ f)
  let : Algebra R (V.X i) := φ.hom.toAlgebra
  have hfp : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Algebra.FinitePresentation R (V.X i) :=
    RingHom.finitePresentation_algebraMap.mp
      ((LocallyOfFinitePresentation.SpecMap_iff _).mp hfp)
  have : Smooth (pullback.snd (Affine.Construction.affineOver R (V.X i)).hom g) := by
    change Smooth (pullback.snd (Spec.map φ) g)
    rw [hφ]
    exact hsm
  let p : PrimeSpectrum (V.X i) := y
  have hp : Ideal.comap (algebraMap R (V.X i)) p.asIdeal = ⊥ := by
    have heq : PrimeSpectrum.comap φ.hom p = (⊥ : PrimeSpectrum R) := by
      change (Spec.map φ) y = (show PrimeSpectrum R from ⊥)
      rw [hφ]
      change f (V.f i y) = _
      rw [hy]
      exact hx
    exact congrArg PrimeSpectrum.asIdeal heq
  have hySm : y ∈ (V.f i ≫ f).smoothLocus := by
    have h := affine_generic_point_mem_smoothLocus R K (V.X i) p hp
    change y ∈ (Spec.map φ).smoothLocus at h
    simpa only [hφ] using h
  have hyPre : y ∈ (V.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact hySm
  change V.f i y ∈ f.smoothLocus at hyPre
  rw [hy] at hyPre
  exact hyPre

/-- A proper model of a smooth generic fiber becomes smooth after removing
finitely many primes. The construction of the proper model remains a separate step. -/
theorem proper_model_with_smooth_generic_fiber_shrinks
    (R K : Type u) [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    ∃ U : (Spec (CommRingCat.of R)).Opens,
      ((U : Set (Spec (CommRingCat.of R)))ᶜ).Finite ∧
      (show PrimeSpectrum R from ⊥) ∈ U ∧
      Smooth (f ∣_ U) ∧ IsProper (f ∣_ U) :=
  SmoothShrink.Construction.proper_model_smooth_after_shrinking f (generic_point_mem_smoothLocus R K f)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GenericSmoothness.Construction
