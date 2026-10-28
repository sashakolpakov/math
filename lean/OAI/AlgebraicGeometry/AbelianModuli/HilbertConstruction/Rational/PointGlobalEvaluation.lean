import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.AlgebraRationalPointIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkScalarResidue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Point Global Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointGlobalEvaluation

noncomputable section

/-! Evaluation of global functions at an actual rational section has the
structural coefficient map as a right inverse. Generating functions on
an affine scheme then distinguish this point from every other point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}}

def rationalPointGlobalEvaluation (p : X ⟶ Spec (.of K))
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) : Γ(X, ⊤) →+* K :=
  (X.Γevaluation (s (IsLocalRing.closedPoint K)) ≫
    (PointResidue.rationalPointResidueIso p s hs).hom).hom

theorem rationalPointGlobalEvaluation_coefficient (p : X ⟶ Spec (.of K))
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) (c : K) :
    rationalPointGlobalEvaluation p s hs (Coefficient.ModulePresheaf.schemeCoefficientMap p c) = c := by
  have h := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f c)
    (StalkScalarResidue.rationalStalkResidueCoefficient_comp_residueIso p s hs)
  change (PointResidue.rationalPointResidueIso p s hs).hom (StalkScalarResidue.rationalStalkResidueCoefficient p s c) = c at h
  exact h

theorem rationalPointGlobalEvaluation_eq_zero (p : X ⟶ Spec (.of K))
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) (r : Γ(X, ⊤)) :
    rationalPointGlobalEvaluation p s hs r = 0 ↔
      s (IsLocalRing.closedPoint K) ∉ X.basicOpen r := by
  let e := (PointResidue.rationalPointResidueIso p s hs).commRingCatIsoToRingEquiv
  change e (X.Γevaluation (s (IsLocalRing.closedPoint K)) r) = 0 ↔ _
  constructor
  · intro h
    apply (X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) (s (IsLocalRing.closedPoint K)) trivial r).mp
    apply e.injective
    simpa only [map_zero] using h
  · intro h
    rw [(X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) (s (IsLocalRing.closedPoint K)) trivial r).mpr h, map_zero]

theorem globalSection_mem_toSpecPrime (x : X) (r : Γ(X, ⊤)) :
    r ∈ (X.toSpecΓ x).asIdeal ↔ x ∉ X.basicOpen r := by
  have h := (congrArg (fun U : X.Opens => x ∈ U)
    (Scheme.toSpecΓ_preimage_basicOpen X r)).to_iff
  change (r ∉ (X.toSpecΓ x).asIdeal ↔ x ∈ X.basicOpen r) at h
  simpa only [not_not] using not_congr h

theorem rationalPointGlobalEvaluation_kernel (p : X ⟶ Spec (.of K))
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    RingHom.ker (rationalPointGlobalEvaluation p s hs) =
      (X.toSpecΓ (s (IsLocalRing.closedPoint K))).asIdeal := by
  ext r
  exact (rationalPointGlobalEvaluation_eq_zero p s hs r).trans
    (globalSection_mem_toSpecPrime _ r).symm

theorem affineScheme_eq_rationalPoint_of_generators [IsAffine X]
    (p : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _)
    {ι : Type v} (v : ι → Γ(X, ⊤))
    (hv : letI := (Coefficient.ModulePresheaf.schemeCoefficientMap p).toAlgebra;
      Algebra.adjoin K (Set.range v) = ⊤)
    (x : X)
    (hx : ∀ i, x ∉ X.basicOpen
      (v i - Coefficient.ModulePresheaf.schemeCoefficientMap p (rationalPointGlobalEvaluation p s hs (v i)))) :
    x = s (IsLocalRing.closedPoint K) := by
  let := (Coefficient.ModulePresheaf.schemeCoefficientMap p).toAlgebra
  let φ : Γ(X, ⊤) →ₐ[K] K :=
    { __ := rationalPointGlobalEvaluation p s hs
      commutes' := rationalPointGlobalEvaluation_coefficient p s hs }
  have : (X.toSpecΓ x).asIdeal.IsPrime := (X.toSpecΓ x).isPrime
  have hP : (X.toSpecΓ x).asIdeal = RingHom.ker φ.toRingHom :=
    Generated.AlgebraRationalPointIdeal.generatedAlgebra_prime_eq_rationalPoint v hv φ (X.toSpecΓ x).asIdeal
      (fun i => (globalSection_mem_toSpecPrime x _).mpr (hx i))
  have he : X.toSpecΓ x = X.toSpecΓ (s (IsLocalRing.closedPoint K)) := by
    apply PrimeSpectrum.ext
    exact hP.trans (rationalPointGlobalEvaluation_kernel p s hs)
  have he' : X.isoSpec.hom x = X.isoSpec.hom (s (IsLocalRing.closedPoint K)) := he
  have h := congrArg (fun y => X.isoSpec.inv y) he'
  simpa using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointGlobalEvaluation
