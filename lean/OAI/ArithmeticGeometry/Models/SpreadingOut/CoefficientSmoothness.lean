import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericSmoothness
import OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersion

/-! # Coefficient Smoothness -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness.Construction

noncomputable section

/-! Smoothness of a proper generic fiber spreads after one more finite
enlargement of its coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

/-- Over an integral affine base, the proper image of the nonsmooth locus
can be removed by inverting one nonzero element. -/
theorem proper_smooth_generic_fiber_has_smooth_basicOpen
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    ∃ (a : R), a ≠ 0 ∧
      Smooth (f ∣_ (PrimeSpectrum.basicOpen a : (Spec (.of R)).Opens)) := by
  let Z : Set (PrimeSpectrum R) := f '' (f.smoothLocus : Set X)ᶜ
  have hZ : IsClosed Z := f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl
  have hη : (⊥ : PrimeSpectrum R) ∉ Z := by
    rintro ⟨x, hx, heq⟩
    exact hx (GenericSmoothness.Construction.generic_point_mem_smoothLocus R K f x heq)
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  have ha : ∃ a ∈ s, a ≠ 0 := by
    by_contra! h
    apply hη
    rw [hs]
    intro a ha
    exact h a ha
  obtain ⟨a, has, ha⟩ := ha
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen a
  have hpre : f ⁻¹ᵁ U ≤ f.smoothLocus := by
    intro x hx
    by_contra hn
    have hz : f x ∈ Z := ⟨x, hn, rfl⟩
    rw [hs] at hz
    exact hx (hz has)
  have hsm : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := SmoothShrink.Construction.smooth_on_open_in_smoothLocus f _ hpre
  have hscomp : Smooth ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact hsm
  have hpb : IsPullback (𝟙 (f ⁻¹ᵁ U).toScheme) (f ∣_ U)
      ((f ∣_ U) ≫ U.ι) U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  exact ⟨a, ha, MorphismProperty.of_isPullback hpb hscomp⟩

/-- A pullback whose base lands in a smooth restriction is smooth. -/
theorem smooth_pullback_of_range_subset
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (U : S.Opens) [Smooth (f ∣_ U)]
    (hg : Set.range g ⊆ (U : Set S)) : Smooth (pullback.snd f g) := by
  let q := IsOpenImmersion.lift U.ι g (by simpa using hg)
  have hq : q ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hrange : Set.range (pullback.fst f g) ⊆ (f ⁻¹ᵁ U : Set X) := by
    rintro _ ⟨x, rfl⟩
    change f (pullback.fst f g x) ∈ U
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact hg (Set.mem_range_self _)
  let p := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (pullback.fst f g)
    (by simpa using hrange)
  have hp : p ≫ (f ⁻¹ᵁ U).ι = pullback.fst f g := IsOpenImmersion.lift_fac _ _ _
  have hcart : IsPullback p (pullback.snd f g) (f ∣_ U) q := by
    apply IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f U).flip
    · rw [hp, hq]
      exact IsPullback.of_hasPullback f g
    · apply (cancel_mono U.ι).mp
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hp,
        Category.assoc (pullback.snd f g) q U.ι, hq]
      exact pullback.condition
  exact MorphismProperty.of_isPullback hcart inferInstance

/-- Enlarging a coefficient set can make any nonzero old coefficient a unit. -/
theorem specMap_range_subset_basicOpen_of_unit
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (a : R) (ha : IsUnit (φ a)) :
    Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆
      ((show (Spec (.of R)).Opens from PrimeSpectrum.basicOpen a) :
        Set (Spec (.of R))) := by
  rintro _ ⟨p, rfl⟩
  let q : PrimeSpectrum A := p
  exact q.asIdeal.notMem_of_isUnit ha

def reciprocalCoefficientSet
    {K : Type u} [Field K] (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) : Finset K := by
  classical
  exact insert (a.val⁻¹) s

theorem subset_reciprocalCoefficientSet
    {K : Type u} [Field K] (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :
    s ⊆ reciprocalCoefficientSet s a := by
  classical
  exact Finset.subset_insert _ _

def reciprocalCoefficientHom
    {K : Type u} [Field K] (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :
    CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s →ₐ[𝓞 K]
      CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K (reciprocalCoefficientSet s a) :=
  Subalgebra.inclusion (Algebra.adjoin_mono
    (Finset.coe_subset.mpr (subset_reciprocalCoefficientSet s a)))

theorem subalgebra_unit_of_inverse_mem
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (A : Subalgebra R K) (a : A) (ha : a.val ≠ 0) (h : a.val⁻¹ ∈ A) : IsUnit a := by
  refine ⟨⟨a, ⟨a.val⁻¹, h⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ ha
  · apply Subtype.ext
    exact inv_mul_cancel₀ ha

theorem reciprocalCoefficientHom_coe
    {K : Type u} [Field K] (s : Finset K)
    (a b : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :
    (reciprocalCoefficientHom s a b).val = b.val :=
  Subalgebra.coe_inclusion _ b

theorem inverse_mem_reciprocalCoefficientRing
    {K : Type u} [Field K] (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :
    a.val⁻¹ ∈ CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K (reciprocalCoefficientSet s a) := by
  classical
  exact Algebra.subset_adjoin (Finset.mem_insert_self _ _)

theorem reciprocalCoefficientHom_isUnit
    {K : Type u} [Field K] (s : Finset K)
    (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) (ha : a ≠ 0) :
    IsUnit (reciprocalCoefficientHom s a a) := by
  classical
  apply subalgebra_unit_of_inverse_mem
  · rw [reciprocalCoefficientHom_coe]
    exact fun h ↦ ha (Subtype.ext h)
  · rw [reciprocalCoefficientHom_coe]
    exact inverse_mem_reciprocalCoefficientRing s a

theorem reciprocalCoefficientBaseMap_eq
    {K : Type u} [Field K] (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :
    CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K (subset_reciprocalCoefficientSet s a) =
      Spec.map (CommRingCat.ofHom (reciprocalCoefficientHom s a).toRingHom) := rfl

theorem coefficient_base_eventually_in_basicOpen
    {K : Type u} [Field K] [NumberField K] (s : Finset K)
    (a : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) (ha : a ≠ 0) :
    ∃ (t : Finset K) (h : s ⊆ t),
      Set.range (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) ⊆
        ((show (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s).Opens from PrimeSpectrum.basicOpen a) :
          Set (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) := by
  refine ⟨reciprocalCoefficientSet s a, subset_reciprocalCoefficientSet s a, ?_⟩
  rw [reciprocalCoefficientBaseMap_eq]
  exact specMap_range_subset_basicOpen_of_unit (reciprocalCoefficientHom s a).toRingHom
    a (reciprocalCoefficientHom_isUnit s a ha)

theorem proper_coefficient_model_eventually_smooth
    {K : Type u} [Field K] [NumberField K] {s : Finset K}
    (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) [IsProper M.hom]
    [Smooth ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M).hom] :
    ∃ (t : Finset K) (h : s ⊆ t),
      Smooth ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj M).hom := by
  have := ModelFiniteness.Constructions.Foundations.coefficientBase_locallyNoetherian K s
  have : Smooth (pullback.snd M.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) K)))) :=
    ‹Smooth ((Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M).hom›
  obtain ⟨a, ha, hsm⟩ := proper_smooth_generic_fiber_has_smooth_basicOpen
    (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) K M.hom
  obtain ⟨t, h, ht⟩ := coefficient_base_eventually_in_basicOpen s a ha
  have := hsm
  exact ⟨t, h, smooth_pullback_of_range_subset M.hom
    (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) (PrimeSpectrum.basicOpen a) ht⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientSmoothness.Construction
