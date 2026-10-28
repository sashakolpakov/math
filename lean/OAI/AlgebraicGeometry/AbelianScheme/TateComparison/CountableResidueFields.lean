import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableComplexEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Countable Residue Fields -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableResidueFields

noncomputable section

/-! Countable fields of definition for geometric points of a scheme
locally of finite type over a countable field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem countable_finiteType (R A : Type) [CommRing R] [CommRing A]
    [Countable R] [Algebra R A] [Algebra.FiniteType R A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  have : Countable (MvPolynomial (Fin n) R) :=
    Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max.trans
      (sup_le (sup_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  exact hf.countable

theorem countable_localization (R A : Type) [CommRing R] [CommRing A]
    [Countable R] (M : Submonoid R) [Algebra R A] [IsLocalization M A] :
    Countable A := by
  have h : Function.Surjective (Function.uncurry (IsLocalization.mk' (M := M) A)) :=
    fun x => by simpa using IsLocalization.exists_mk'_eq M x
  exact h.countable

theorem countable_ideal_residueField (R : Type) [CommRing R] [Countable R]
    (p : Ideal R) [p.IsPrime] : Countable p.ResidueField := by
  have : Countable (R ⧸ p) := (Ideal.Quotient.mk_surjective (I := p)).countable
  exact countable_localization (R ⧸ p) p.ResidueField (nonZeroDivisors (R ⧸ p))

theorem countable_scheme_residueField (K : Type) [Field K] [Countable K]
    {X : Scheme} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X) :
    Countable (X.residueField x) := by
  obtain ⟨R, i, hi, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  let : IsOpenImmersion i := hi
  let φ := Spec.preimage (i ≫ f)
  have hφ : Spec.map φ = i ≫ f := Spec.map_preimage _
  let : Algebra K R := φ.hom.toAlgebra
  have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have : Algebra.FiniteType K R :=
    RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp
      (inferInstance : LocallyOfFiniteType (Spec.map φ)))
  have : Countable R := countable_finiteType K R
  have : y.asIdeal.IsPrime := y.isPrime
  have : Countable y.asIdeal.ResidueField := countable_ideal_residueField R y.asIdeal
  have : Countable ((Spec R).residueField y) :=
    (Scheme.Spec.residueFieldIso R y).commRingCatIsoToRingEquiv.injective.countable
  have hc : Countable (X.residueField (i y)) :=
    (i.residueFieldMap y).hom.injective.countable
  rwa [hy] at hc

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableResidueFields
