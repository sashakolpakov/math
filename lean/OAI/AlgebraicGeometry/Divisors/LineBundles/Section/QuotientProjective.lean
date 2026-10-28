import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalFinite
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalBasis

/-! # Quotient Projective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientProjective.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual section conormal is finite projective over its quotient ring -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A]

instance sectionQuotient_inversePair :
    RingHomInvPair (ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm.toRingHom (ConormalBasis.BundleCycles.sectionQuotientEquiv A B).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (ConormalBasis.BundleCycles.sectionQuotientEquiv A B)

instance sectionQuotient_forwardPair :
    RingHomInvPair (ConormalBasis.BundleCycles.sectionQuotientEquiv A B).toRingHom (ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (ConormalBasis.BundleCycles.sectionQuotientEquiv A B)

def sectionQuotientConormalEquiv :
    (RingHom.ker (algebraMap B A)).Cotangent ≃ₛₗ[(ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm.toRingHom]
      (RingHom.ker (algebraMap B A)).Cotangent where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := (ConormalBasis.BundleCycles.sectionQuotientEquiv_smul A B a m).symm

variable [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]

omit [Algebra.EssFiniteType A B] in
theorem sectionQuotientConormal_projective :
    Module.Projective (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent :=
  Module.Projective.of_equiv (sectionQuotientConormalEquiv A B)

theorem sectionQuotientConormal_finite :
    Module.Finite (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent := by
  have := ConormalFinite.BundleCycles.sectionConormal_finite A B
  exact Module.Finite.of_surjective (sectionQuotientConormalEquiv A B).toLinearMap
    (sectionQuotientConormalEquiv A B).surjective

theorem sectionQuotientConormal_finitePresentation :
    Module.FinitePresentation (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent := by
  have := sectionQuotientConormal_finite A B
  have := sectionQuotientConormal_projective A B
  exact Module.finitePresentation_of_projective _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientProjective.BundleCycles
