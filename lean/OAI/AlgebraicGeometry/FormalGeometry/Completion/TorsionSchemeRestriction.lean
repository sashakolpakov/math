import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleHom
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MultiplicationDescent

/-! # Torsion Scheme Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionSchemeRestriction.Construction

noncomputable section

/-! The actual torsion-scheme restriction detects divisibility over the original field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

/-- Actual maps from the torsion scheme into A whose image lies in that torsion scheme. -/
def torsionSchemeSections (n : ℕ) : Subgroup (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n ⟶ A) :=
  (powMonoidHom n).ker

/-- Restriction of an actual endomorphism to the entire scheme-theoretic torsion kernel. -/
def algebraicEndTorsionRestriction (n : ℕ) :
    Endomorphisms.Construction.AlgebraicEnd A →+ Additive (torsionSchemeSections A n) where
  toFun f := Additive.ofMul ⟨AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f.toMul.hom.hom, by
    change (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f.toMul.hom.hom) ^ n = 1
    have hι : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ^ n = 1 :=
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨𝟙 _, Category.id_comp _⟩
    rw [← MonObj.pow_comp, hι, MonObj.one_comp]⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact MonObj.comp_one _
  map_add' f g := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact MonObj.comp_mul _ _ _

/-- The target of restriction is finite over every field, by the actual finite-etale kernel. -/
theorem torsionSchemeSections_finite [IsProper A.hom] [Smooth A.hom]
    (n : ℕ) (hn : (n : K) ≠ 0) : Finite (torsionSchemeSections A n) := by
  have := (Multiplication.Construction.torsionScheme_finite_etale A n hn).1
  have := (Multiplication.Construction.torsionScheme_finite_etale A n hn).2
  have := Completion.Finite.EtaleHom.Construction.finite_etale_hom (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n)
  let t : torsionSchemeSections A n → (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n ⟶ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) :=
    fun a => AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n a.val a.property
  apply Finite.of_injective t
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun f => f ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) h
  simpa only [t, AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι] using he

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- The kernel of actual torsion-scheme restriction is precisely n End(A) over the ground field. -/
theorem algebraicEndTorsionRestriction_eq_zero_iff
    (n : ℕ) (hn : (n : K) ≠ 0) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndTorsionRestriction A n f = 0 ↔ ∃ g : Endomorphisms.Construction.AlgebraicEnd A, n • g = f := by
  constructor
  · intro hf
    have hkill : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ f.toMul.hom.hom = 1 :=
      congrArg (fun a : Additive (torsionSchemeSections A n) => a.toMul.val) hf
    obtain ⟨g, hgmon, hg⟩ := MultiplicationDescent.Construction.groupHom_descends_multiplication A n hn f.toMul.hom.hom hkill
    have : IsMonHom g := hgmon
    refine ⟨Additive.ofMul (Grp.ofHom g), ?_⟩
    apply Additive.toMul.injective
    apply Grp.hom_ext
    rw [Multiplication.Construction.algebraicEnd_nsmul_hom]
    change g ^ n = f.toMul.hom.hom
    simpa only [MonObj.pow_comp, Category.id_comp] using hg
  · rintro ⟨g, rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ≫ (n • g).toMul.hom.hom = 1
    have hι : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n ^ n = 1 :=
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff n (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).mp ⟨𝟙 _, Category.id_comp _⟩
    rw [Multiplication.Construction.algebraicEnd_nsmul_hom, MonObj.comp_pow, ← MonObj.pow_comp, hι, MonObj.one_comp]

/-- The divisibility subgroup is the kernel of restriction to the actual torsion scheme. -/
theorem algebraicEnd_nsmul_range_eq_restriction_ker (n : ℕ) (hn : (n : K) ≠ 0) :
    (nsmulAddMonoidHom n : Endomorphisms.Construction.AlgebraicEnd A →+ Endomorphisms.Construction.AlgebraicEnd A).range =
      (algebraicEndTorsionRestriction A n).ker := by
  ext f
  exact (algebraicEndTorsionRestriction_eq_zero_iff A n hn f).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionSchemeRestriction.Construction
