import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.NormDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField

/-! # Fraction Norm Transport -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FractionNormTransport.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the affine norm coefficient in the specified fraction fields
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

attribute [local instance] FractionRing.liftAlgebra

variable (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Module.IsTorsionFree R S]
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]

theorem fractionExtension_square :
    (algebraMap K L).comp (FractionRing.algEquiv R K).toRingHom =
      (FractionRing.algEquiv S L).toRingHom.comp
        (algebraMap (FractionRing R) (FractionRing S)) := by
  apply IsFractionRing.ringHom_ext (A := R)
  intro a
  change algebraMap K L (FractionRing.algEquiv R K (algebraMap R (FractionRing R) a)) =
    FractionRing.algEquiv S L (algebraMap (FractionRing R) (FractionRing S)
      (algebraMap R (FractionRing R) a))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R K L,
    ← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
    IsScalarTower.algebraMap_apply R S (FractionRing S), AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply R S L]

theorem fractionNorm_transport (g : FractionRing S) :
    FractionRing.algEquiv R K (Algebra.norm (FractionRing R) g) =
      Algebra.norm K (FractionRing.algEquiv S L g) := by
  exact (RingEquiv.eq_symm_apply (FractionRing.algEquiv R K).toRingEquiv).mp
    (Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv R K).toRingEquiv
      (FractionRing.algEquiv S L).toRingEquiv (fractionExtension_square R S K L) g)

theorem fractionNorm_order [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (g : FractionRing S) :
    Ring.ordFrac R (Algebra.norm (FractionRing R) g) =
      Ring.ordFrac R (Algebra.norm K (FractionRing.algEquiv S L g)) := by
  have ht := RationalDivisorRestriction.BundleCycles.ringOrderFrac_equiv (RingEquiv.refl R) (FractionRing.algEquiv R K).toRingEquiv
    (fun a => (FractionRing.algEquiv R K).commutes a) (Algebra.norm (FractionRing R) g)
  exact ht.symm.trans (congrArg (Ring.ordFrac R) (fractionNorm_transport R S K L g))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FractionNormTransport.BundleCycles
