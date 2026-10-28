import OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients
import Mathlib.RingTheory.Ideal.Cotangent
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension

/-! # Cone Symmetric -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the canonical map from conormal vectors to the actual normal-cone algebra -/

open _root_.Polynomial

variable {R : Type} [CommRing R] (I : Ideal R)

def reesDegreeOne : I →ₗ[R] reesAlgebra I where
  toFun r := ⟨monomial 1 r.1, reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using r.2)⟩
  map_add' r s := Subtype.ext (map_add (monomial 1) r.1 s.1)
  map_smul' r s := Subtype.ext ((monomial 1 : R →ₗ[R] R[X]).map_smul r s.1)

def normalConeDegreeOne : I →ₗ[R] Cone.BundleCycles.NormalConeRing I :=
  (Ideal.Quotient.mkₐ R (Cone.BundleCycles.normalConeIdeal I)).toLinearMap.comp (reesDegreeOne I)

theorem normalConeDegreeOne_eq_zero (r : I) (hr : r.1 ∈ I ^ 2) : normalConeDegreeOne I r = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff I (reesDegreeOne I r)).mpr
  intro n
  change (monomial 1 r.1).coeff n ∈ I ^ (n + 1)
  rw [coeff_monomial]
  split_ifs with hn
  · subst n
    exact hr
  · exact Ideal.zero_mem _

def normalConeConormalLinear : I.Cotangent →ₗ[R] Cone.BundleCycles.NormalConeRing I :=
  (I • (⊤ : Submodule R I)).liftQ (normalConeDegreeOne I) (by
    intro r hr
    apply normalConeDegreeOne_eq_zero I r
    apply (I.mem_toCotangent_ker).mp
    exact (Submodule.ker_mkQ (I • (⊤ : Submodule R I))).symm ▸ hr)

abbrev normalConeQuotientAlgebra : Algebra (R ⧸ I) (Cone.BundleCycles.NormalConeRing I) :=
  @RingHom.toAlgebra (R ⧸ I) (Cone.BundleCycles.NormalConeRing I) _ _ (Cone.BundleCycles.normalConeBaseMap I)

attribute [local instance] normalConeQuotientAlgebra

instance normalConeQuotient_scalarTower : IsScalarTower R (R ⧸ I) (Cone.BundleCycles.NormalConeRing I) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def normalConeConormalMap : I.Cotangent →ₗ[R ⧸ I] Cone.BundleCycles.NormalConeRing I :=
  (LinearMap.extendScalarsOfSurjectiveEquiv (Ideal.Quotient.mk_surjective :
    Function.Surjective (algebraMap R (R ⧸ I)))) (normalConeConormalLinear I)

theorem normalConeConormalMap_toCotangent (r : I) :
    normalConeConormalMap I (I.toCotangent r) =
      Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) (reesDegreeOne I r) := rfl

def normalConeSymmetricData :
    {g : SymmetricAlgebra (R ⧸ I) I.Cotangent →+* Cone.BundleCycles.NormalConeRing I //
      (∀ r : I, g (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent (I.toCotangent r)) =
        Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) (reesDegreeOne I r)) ∧
      ∀ a : R ⧸ I, g (algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent) a) = Cone.BundleCycles.normalConeBaseMap I a} := by
  let e := @Symmetric.Extension.BundleCycles.symmetricExtension (R ⧸ I) I.Cotangent (Cone.BundleCycles.NormalConeRing I) (by infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance) (normalConeQuotientAlgebra I)
    (normalConeConormalMap I)
  refine ⟨e.val, ?_, ?_⟩
  · intro r
    exact (e.property.1 (I.toCotangent r)).trans (normalConeConormalMap_toCotangent I r)
  · intro a
    exact e.property.2 a

def normalConeSymmetricMap : SymmetricAlgebra (R ⧸ I) I.Cotangent →+* Cone.BundleCycles.NormalConeRing I :=
  (normalConeSymmetricData I).val

end

section

/-! # LineBundleCycles: the canonical conormal symmetric map on its actual generators -/

variable {R : Type} [CommRing R] (I : Ideal R)
attribute [local instance] normalConeQuotientAlgebra

theorem normalConeSymmetricMap_generator (r : I) :
    normalConeSymmetricMap I (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent (I.toCotangent r)) =
      Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) (reesDegreeOne I r) :=
  (normalConeSymmetricData I).property.1 r

theorem normalConeSymmetricMap_algebraMap (a : R ⧸ I) :
    normalConeSymmetricMap I (algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent) a) =
      Cone.BundleCycles.normalConeBaseMap I a :=
  (normalConeSymmetricData I).property.2 a

end

/-! # LineBundleCycles: the normal cone is the actual quotient of its conormal symmetric algebra -/

open _root_.Polynomial
open scoped BigOperators

variable {R : Type} [CommRing R] (I : Ideal R)

attribute [local instance] normalConeQuotientAlgebra

def reesMonomial (n : ℕ) (r : R) (hr : r ∈ I ^ n) : reesAlgebra I :=
  ⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩

theorem symmetricRange_contains_monomial (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ∃ p : reesAlgebra I, Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) p ∈ (normalConeSymmetricMap I).rangeS ∧
      p.val = monomial n r := by
  induction n generalizing r with
  | zero =>
    refine ⟨algebraMap R (reesAlgebra I) r, ?_, rfl⟩
    exact ⟨algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent) (Ideal.Quotient.mk I r),
      normalConeSymmetricMap_algebraMap I (Ideal.Quotient.mk I r)⟩
  | succ n ih =>
    rw [pow_succ'] at hr
    refine Submodule.smul_induction_on hr ?_ ?_
    · intro a ha b hb
      obtain ⟨p, hp, he⟩ := ih b hb
      have ha' : Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) (reesDegreeOne I ⟨a, ha⟩) ∈
          (normalConeSymmetricMap I).rangeS :=
        ⟨SymmetricAlgebra.ι (R ⧸ I) I.Cotangent (I.toCotangent ⟨a, ha⟩), normalConeSymmetricMap_generator I _⟩
      refine ⟨reesDegreeOne I ⟨a, ha⟩ * p, ?_, ?_⟩
      · rw [map_mul]
        exact (normalConeSymmetricMap I).rangeS.mul_mem ha' hp
      · change monomial 1 a * p.val = monomial (n + 1) (a * b)
        rw [he, monomial_mul_monomial, Nat.add_comm 1 n]
    · intro a b ha hb
      obtain ⟨p, hp, he⟩ := ha
      obtain ⟨q, hq, hf⟩ := hb
      refine ⟨p + q, ?_, ?_⟩
      · rw [map_add]
        exact (normalConeSymmetricMap I).rangeS.add_mem hp hq
      · change p.val + q.val = _
        rw [he, hf, map_add]

theorem normalConeMonomial_mem_symmetricRange (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) (reesMonomial I n r hr) ∈ (normalConeSymmetricMap I).rangeS := by
  obtain ⟨p, hp, he⟩ := symmetricRange_contains_monomial I n r hr
  have h : p = reesMonomial I n r hr := Subtype.ext he
  exact h ▸ hp

theorem normalConeSymmetricMap_surjective : Function.Surjective (normalConeSymmetricMap I) := by
  classical
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) p ∈ (normalConeSymmetricMap I).rangeS
  have he : p = ∑ n ∈ p.val.support, reesMonomial I n (p.val.coeff n) (p.property n) := by
    apply Subtype.ext
    change p.val = (reesAlgebra I).val (∑ n ∈ p.val.support, reesMonomial I n (p.val.coeff n) (p.property n))
    rw [map_sum]
    exact p.val.as_sum_support
  rw [he, map_sum]
  exact (normalConeSymmetricMap I).rangeS.sum_mem fun n hn => normalConeMonomial_mem_symmetricRange I n _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric.BundleCycles
