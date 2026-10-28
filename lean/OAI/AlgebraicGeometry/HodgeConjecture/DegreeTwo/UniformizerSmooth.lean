import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothDVR
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Smooth.Locus

/-! # Uniformizer Smooth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizerSmooth.Constructions

noncomputable section

/-!
# DegreeTwo: the hypersurface cut out by a local uniformizer is generically smooth

Localization of the actual principal quotient is the residue field of the
DVR. Over a perfect field that local ring is formally smooth, so the actual
hypersurface has a smooth neighborhood of the codimension-one point.
-/

universe u v

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]
variable [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)]

/-- Localizing the principal quotient by a genuine local uniformizer gives
the actual residue field of the codimension-one DVR. -/
theorem uniformizerQuotient_localization_isField (a : R)
    (ha : Irreducible (algebraMap R (Localization.AtPrime P) a))
    (Q : Ideal (R ⧸ Ideal.span {a})) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk (Ideal.span {a})) = P) :
    IsField (Localization.AtPrime Q) := by
  let A := Localization.AtPrime P
  let I := Ideal.span ({a} : Set R)
  let B := A ⧸ I.map (algebraMap R A)
  have hI : I.map (algebraMap R A) = IsLocalRing.maximalIdeal A := by
    rw [Ideal.map_span, Set.image_singleton]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp ha |>.symm
  have hB : IsField B := by
    change IsField (A ⧸ I.map (algebraMap R A))
    rw [hI]
    let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
    exact Field.toIsField (A ⧸ IsLocalRing.maximalIdeal A)
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl = Q.primeCompl := by
    change P.primeCompl.map (Ideal.Quotient.mk I) = Q.primeCompl
    have hc : P.primeCompl = (Q.comap (Ideal.Quotient.mk I)).primeCompl := by
      ext r
      change r ∉ P ↔ r ∉ Q.comap (Ideal.Quotient.mk I)
      rw [hQ]
    rw [hc]
    exact Ideal.map_primeCompl_comap_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q
  let : IsLocalization Q.primeCompl B := by
    rw [← hM]
    infer_instance
  exact (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) B).toRingEquiv.isField hB

/-- A local uniformizer cuts out a smooth hypersurface at its actual
quotient prime; perfectness supplies formal smoothness of the residue field. -/
theorem uniformizerQuotient_isSmoothAt (K : Type v) [Field K] [PerfectField K]
    [Algebra K R] [Algebra.FiniteType K R] (a : R)
    (ha : Irreducible (algebraMap R (Localization.AtPrime P) a))
    (Q : Ideal (R ⧸ Ideal.span {a})) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk (Ideal.span {a})) = P) :
    Algebra.IsSmoothAt K Q := by
  let : Field (Localization.AtPrime Q) := (uniformizerQuotient_localization_isField P a ha Q hQ).toField
  exact Algebra.FormallySmooth.of_perfectField

/-- The actual hypersurface has a principal smooth neighborhood through the
quotient point, with the neighborhood element lifted to the ambient ring. -/
theorem uniformizerQuotient_smooth_neighborhood (K : Type v) [Field K] [PerfectField K]
    [Algebra K R] [Algebra.FinitePresentation K R] (a : R)
    (ha : Irreducible (algebraMap R (Localization.AtPrime P) a))
    (Q : Ideal (R ⧸ Ideal.span {a})) [Q.IsPrime]
    (hQ : Q.comap (Ideal.Quotient.mk (Ideal.span {a})) = P) :
    ∃ b : R, b ∉ P ∧ Algebra.Smooth K (Localization.Away (Ideal.Quotient.mk (Ideal.span {a}) b)) := by
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span {a}) :=
    Algebra.FinitePresentation.quotient (show (Ideal.span ({a} : Set R)).FG from ⟨{a}, by simp⟩)
  let : Algebra.IsSmoothAt K Q := uniformizerQuotient_isSmoothAt P K a ha Q hQ
  obtain ⟨q, hq, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth K Q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨b, ?_, hsm⟩
  intro hb
  apply hq
  change b ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {a}))
  rw [hQ]
  exact hb

/-- The quotient prime is determined by the ambient prime, so no additional
quotient-point or smoothness data is required from the caller. -/
theorem uniformizer_hypersurface_smooth_neighborhood (K : Type v) [Field K] [PerfectField K]
    [Algebra K R] [Algebra.FinitePresentation K R] (a : R)
    (ha : Irreducible (algebraMap R (Localization.AtPrime P) a)) :
    ∃ b : R, b ∉ P ∧ Algebra.Smooth K (Localization.Away (Ideal.Quotient.mk (Ideal.span {a}) b)) := by
  classical
  have haP : a ∈ P := by
    by_contra h
    exact ha.not_isUnit (IsLocalization.map_units (Localization.AtPrime P) (⟨a, h⟩ : P.primeCompl))
  let I := Ideal.span ({a} : Set R)
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr haP
  let Q : Ideal (R ⧸ I) := P.map (Ideal.Quotient.mk I)
  let : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (show RingHom.ker (Ideal.Quotient.mk I) ≤ P by simpa only [Ideal.mk_ker] using hIP)
  have hQ : Q.comap (Ideal.Quotient.mk I) = P := by
    change (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    change P ⊔ RingHom.ker (Ideal.Quotient.mk I) = P
    rw [Ideal.mk_ker, sup_eq_left.mpr hIP]
  exact uniformizerQuotient_smooth_neighborhood P K a ha Q hQ

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizerSmooth.Constructions
