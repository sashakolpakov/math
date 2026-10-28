import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SemilinearMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction

/-! # Conormal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalRestriction.BundleCycles

noncomputable section

/-! Actual graded restrictions of augmented conormal symmetric algebras. -/

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

def augmentedConormalGradedRestriction (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    Symmetric.Grading.BundleCycles.symmetricGrading (R ⧸ I) ((R ⧸ I) × I.Cotangent) →+*ᵍ
      Symmetric.Grading.BundleCycles.symmetricGrading (S ⧸ J) ((S ⧸ J) × J.Cotangent) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (Ideal.quotientMap J f hf)
    (SemilinearMap.BundleCycles.augmentedSemilinearMap (Ideal.quotientMap J f hf) (Conormal.ConormalRestriction.BundleCycles.cotangentCoefficientMap I J f hf))

theorem augmentedConormalGradedRestriction_algebraMap (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I ≤ J.comap f) (r : R ⧸ I) :
    augmentedConormalGradedRestriction I J f hf (algebraMap (R ⧸ I) _ r) =
      algebraMap (S ⧸ J) _ (Ideal.quotientMap J f hf r) :=
  Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap _ _ r

theorem augmentedConormalGradedRestriction_generator (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I ≤ J.comap f) (r : R ⧸ I) (a : I) :
    augmentedConormalGradedRestriction I J f hf
      (SymmetricAlgebra.ι (R ⧸ I) ((R ⧸ I) × I.Cotangent) (r, I.toCotangent a)) =
    SymmetricAlgebra.ι (S ⧸ J) ((S ⧸ J) × J.Cotangent)
      (Ideal.quotientMap J f hf r, J.toCotangent ⟨f a.val, hf a.property⟩) :=
  Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator _ _ _

theorem augmentedConormalGradedRestriction_congr (I : Ideal R) (J : Ideal S)
    {f g : R →+* S} (h : f = g) (hf : I ≤ J.comap f) (hg : I ≤ J.comap g) :
    augmentedConormalGradedRestriction I J f hf = augmentedConormalGradedRestriction I J g hg := by
  subst g
  rfl

theorem augmentedConormalGradedRestriction_id (I : Ideal R) :
    augmentedConormalGradedRestriction I I (RingHom.id R) (Conormal.ConormalRestriction.BundleCycles.conormalIdeal_le_comap_id I) =
      GradedRingHom.id (Symmetric.Grading.BundleCycles.symmetricGrading (R ⧸ I) ((R ⧸ I) × I.Cotangent)) := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact augmentedConormalGradedRestriction_algebraMap I I (RingHom.id R)
      (Conormal.ConormalRestriction.BundleCycles.conormalIdeal_le_comap_id I) (Ideal.Quotient.mk I r)
  · rintro ⟨r, a⟩
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact augmentedConormalGradedRestriction_generator I I (RingHom.id R)
      (Conormal.ConormalRestriction.BundleCycles.conormalIdeal_le_comap_id I) (Ideal.Quotient.mk I r) a

theorem augmentedConormalGradedRestriction_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (augmentedConormalGradedRestriction J K g hg).comp (augmentedConormalGradedRestriction I J f hf) =
      augmentedConormalGradedRestriction I K (g.comp f) (Conormal.ConormalRestriction.BundleCycles.conormalIdeal_le_comap_comp I J K f g hf hg) := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact (congrArg (augmentedConormalGradedRestriction J K g hg)
      (augmentedConormalGradedRestriction_algebraMap I J f hf (Ideal.Quotient.mk I r))).trans
        ((augmentedConormalGradedRestriction_algebraMap J K g hg
          (Ideal.quotientMap J f hf (Ideal.Quotient.mk I r))).trans
          (augmentedConormalGradedRestriction_algebraMap I K (g.comp f)
            (Conormal.ConormalRestriction.BundleCycles.conormalIdeal_le_comap_comp I J K f g hf hg) (Ideal.Quotient.mk I r)).symm)
  · rintro ⟨r, a⟩
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact (congrArg (augmentedConormalGradedRestriction J K g hg)
      (augmentedConormalGradedRestriction_generator I J f hf (Ideal.Quotient.mk I r) a)).trans
        ((augmentedConormalGradedRestriction_generator J K g hg
          (Ideal.quotientMap J f hf (Ideal.Quotient.mk I r)) ⟨f a.val, hf a.property⟩).trans
          (augmentedConormalGradedRestriction_generator I K (g.comp f)
            (Conormal.ConormalRestriction.BundleCycles.conormalIdeal_le_comap_comp I J K f g hf hg) (Ideal.Quotient.mk I r) a).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.ConormalRestriction.BundleCycles
