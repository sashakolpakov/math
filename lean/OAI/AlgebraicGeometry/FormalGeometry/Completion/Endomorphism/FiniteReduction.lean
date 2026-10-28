import OAI.AlgebraicGeometry.FormalGeometry.Completion.MultiplicationDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointDetection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionSchemeRestriction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Finite Reduction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteReduction.Construction

noncomputable section

/-! Reduction of the actual endomorphism group modulo n has finite image and the exact kernel n End. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- The kernel of the actual torsion-point action is exactly divisibility by n in the
actual endomorphism group. The divisible endomorphism is constructed by fpqc descent. -/
theorem algebraicEndTorsionPointAction_eq_zero_iff
    (n : ℕ) (hn : (n : K) ≠ 0) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    TorsionPointAction.Construction.algebraicEndTorsionPointAction A n f = 0 ↔ ∃ g : Endomorphisms.Construction.AlgebraicEnd A, n • g = f := by
  constructor
  · intro hf
    obtain ⟨g, hgmon, hg⟩ := MultiplicationDescent.Construction.groupHom_descends_multiplication A n hn f.toMul.hom.hom
      (TorsionPointDetection.Construction.torsion_restriction_eq_one_of_points A n hn f hf)
    have : IsMonHom g := hgmon
    let e : Endomorphisms.Construction.AlgebraicEnd A := Additive.ofMul (Grp.ofHom g)
    refine ⟨e, ?_⟩
    apply Additive.toMul.injective
    apply Grp.hom_ext
    rw [Multiplication.Construction.algebraicEnd_nsmul_hom]
    change g ^ n = f.toMul.hom.hom
    simpa only [MonObj.pow_comp, Category.id_comp] using hg
  · rintro ⟨g, rfl⟩
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.toMul.val ≫ (n • g).toMul.hom.hom = 1
    rw [Multiplication.Construction.algebraicEnd_nsmul_hom, MonObj.comp_pow, ← MonObj.pow_comp,
      show a.toMul.val ^ n = 1 from a.toMul.property, MonObj.one_comp]

/-- The subgroup of n-multiples equals the kernel of the actual torsion representation. -/
theorem algebraicEnd_nsmul_range_eq_torsion_ker (n : ℕ) (hn : (n : K) ≠ 0) :
    (nsmulAddMonoidHom n : Endomorphisms.Construction.AlgebraicEnd A →+ Endomorphisms.Construction.AlgebraicEnd A).range =
      (TorsionPointAction.Construction.algebraicEndTorsionPointAction A n).toAddMonoidHom.ker := by
  ext f
  exact (algebraicEndTorsionPointAction_eq_zero_iff A n hn f).symm

omit [IsAlgClosed K] in
/-- The actual quotient End(A)/n End(A) is finite over every field when n is invertible. -/
theorem algebraicEnd_quotient_nsmul_finite (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite ((Endomorphisms.Construction.AlgebraicEnd A) ⧸ (nsmulAddMonoidHom n : Endomorphisms.Construction.AlgebraicEnd A →+ Endomorphisms.Construction.AlgebraicEnd A).range) := by
  have : Finite (TorsionSchemeRestriction.Construction.torsionSchemeSections A n) := TorsionSchemeRestriction.Construction.torsionSchemeSections_finite A n hn
  rw [TorsionSchemeRestriction.Construction.algebraicEnd_nsmul_range_eq_restriction_ker A n hn]
  exact Finite.of_injective
    (QuotientAddGroup.kerLift (TorsionSchemeRestriction.Construction.algebraicEndTorsionRestriction A n))
    (QuotientAddGroup.kerLift_injective _)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteReduction.Construction
