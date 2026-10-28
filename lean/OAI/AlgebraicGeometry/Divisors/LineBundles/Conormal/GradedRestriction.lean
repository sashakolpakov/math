import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading

/-! # Graded Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.GradedRestriction.BundleCycles

noncomputable section

/-! The actual conormal symmetric restriction respects its intrinsic grading. -/

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

def conormalGradedRestriction (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    Symmetric.Grading.BundleCycles.symmetricGrading (R ⧸ I) I.Cotangent →+*ᵍ Symmetric.Grading.BundleCycles.symmetricGrading (S ⧸ J) J.Cotangent :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (Ideal.quotientMap J f hf) (ConormalRestriction.BundleCycles.cotangentCoefficientMap I J f hf)

theorem conormalGradedRestriction_congr (I : Ideal R) (J : Ideal S)
    {f g : R →+* S} (h : f = g) (hf : I ≤ J.comap f) (hg : I ≤ J.comap g) :
    conormalGradedRestriction I J f hf = conormalGradedRestriction I J g hg := by
  subst g
  rfl

theorem conormalGradedRestriction_id (I : Ideal R) :
    conormalGradedRestriction I I (RingHom.id R) (ConormalRestriction.BundleCycles.conormalIdeal_le_comap_id I) =
      GradedRingHom.id (Symmetric.Grading.BundleCycles.symmetricGrading (R ⧸ I) I.Cotangent) := by
  apply GradedRingHom.coe_ringHom_injective
  exact ConormalRestriction.BundleCycles.conormalSymmetricRestriction_id I

theorem conormalGradedRestriction_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (conormalGradedRestriction J K g hg).comp (conormalGradedRestriction I J f hf) =
      conormalGradedRestriction I K (g.comp f) (ConormalRestriction.BundleCycles.conormalIdeal_le_comap_comp I J K f g hf hg) := by
  apply GradedRingHom.coe_ringHom_injective
  exact ConormalRestriction.BundleCycles.conormalSymmetricRestriction_comp I J K f g hf hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.GradedRestriction.BundleCycles
