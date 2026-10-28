import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothNilCommonReduction

/-! # Pointed Smooth Common Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PointedSmoothCommonResidue

noncomputable section

/-! The pointed smooth isomorphism can be specified using the actual
residue coefficient ring rather than a chosen quotient presentation. -/

universe u v w z t
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  (I : Ideal R) (ρ : R →ₐ[R] S) (hρ : Function.Surjective ρ)
  (hρker : RingHom.ker ρ.toRingHom = I)

def quotientIso : (R ⧸ I) ≃ₐ[R] S :=
  (Ideal.quotientEquivAlgOfEq R hρker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hρ)

theorem quotientIso_mk (r : R) :
    quotientIso I ρ hρ hρker (Ideal.Quotient.mk I r) = ρ r := rfl

variable {C : Type w} [CommRing C] [Algebra R C] (εC : C →ₐ[R] S)

def normalizedSection : C →ₐ[R] R ⧸ I :=
  (quotientIso I ρ hρ hρker).symm.toAlgHom.comp εC

variable {A : Type z} [CommRing A] [Algebra R A]
  (πA : A →ₐ[R] C) (εA : A →ₐ[R] R)

theorem normalized_compatibility (h : εC.comp πA = ρ.comp εA) :
    (normalizedSection I ρ hρ hρker εC).comp πA = (Ideal.Quotient.mkₐ R I).comp εA := by
  apply AlgHom.ext
  intro a
  apply (quotientIso I ρ hρ hρker).injective
  change quotientIso I ρ hρ hρker ((quotientIso I ρ hρ hρker).symm (εC (πA a))) =
    quotientIso I ρ hρ hρker (Ideal.Quotient.mk I (εA a))
  rw [AlgEquiv.apply_symm_apply, quotientIso_mk]
  exact AlgHom.congr_fun h a

variable {B : Type t} [CommRing B] [Algebra R B]
  (hI : IsNilpotent I) [Algebra.FormallySmooth R A] [Module.Flat R B]
  (hA : Function.Surjective πA) (hAker : RingHom.ker πA.toRingHom = I.map (algebraMap R A))
  (πB : B →ₐ[R] C) (hB : Function.Surjective πB)
  (hBker : RingHom.ker πB.toRingHom = I.map (algebraMap R B))
  (εB : B →ₐ[R] R) (hεA : εC.comp πA = ρ.comp εA) (hεB : εC.comp πB = ρ.comp εB)

def equiv : A ≃ₐ[R] B :=
  SmoothNilCommonReduction.Pointed.equiv I hI πA hA hAker πB hB hBker εA εB
    (normalizedSection I ρ hρ hρker εC)
    (normalized_compatibility I ρ hρ hρker εC πA εA hεA)
    (normalized_compatibility I ρ hρ hρker εC πB εB hεB)

theorem reduction_equiv : πB.comp
    (equiv I ρ hρ hρker εC πA εA hI hA hAker πB hB hBker εB hεA hεB).toAlgHom = πA :=
  SmoothNilCommonReduction.Pointed.reduction_equiv I hI πA hA hAker πB hB hBker εA εB
    (normalizedSection I ρ hρ hρker εC)
    (normalized_compatibility I ρ hρ hρker εC πA εA hεA)
    (normalized_compatibility I ρ hρ hρker εC πB εB hεB)

theorem section_equiv : εB.comp
    (equiv I ρ hρ hρker εC πA εA hI hA hAker πB hB hBker εB hεA hεB).toAlgHom = εA :=
  SmoothNilCommonReduction.Pointed.section_equiv I hI πA hA hAker πB hB hBker εA εB
    (normalizedSection I ρ hρ hρker εC)
    (normalized_compatibility I ρ hρ hρker εC πA εA hεA)
    (normalized_compatibility I ρ hρ hρker εC πB εB hεB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PointedSmoothCommonResidue
