import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.ActionFromGenerator
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Torsion Division -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionDivision

noncomputable section

/-! Division of an actual abelian-scheme endomorphism by a tame integer
is equivalent to its vanishing on the actual finite étale torsion scheme.
The quotient morphism and its uniqueness are constructed by fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (c : ℕ)
  (hc : ∀ s : S, IsUnit (c : S.presheaf.stalk s))

include hc in
theorem torsionScheme_finite_etale :
    IsFinite (A.torsionScheme c).hom ∧ Etale (A.torsionScheme c).hom := by
  obtain ⟨hf, he, _⟩ := UnitMultiplication.unit_multiplication_finite_etale_surjective A.scheme c hc
  have : IsFinite (A.multiplication c).left := hf
  have : Etale (A.multiplication c).left := he
  exact ⟨inferInstanceAs (IsFinite
    (CategoryTheory.Limits.pullback.snd (A.multiplication c).left η[A.scheme].left)),
    inferInstanceAs (Etale
      (CategoryTheory.Limits.pullback.snd (A.multiplication c).left η[A.scheme].left))⟩

theorem torsion_zero_of_division (p v : Finite.Actions.GroupEndRing A)
    (hv : (c : Finite.Actions.GroupEndRing A) * v = p) :
    A.torsionInclusion c ≫ p.hom A = 1 := by
  rw [← hv, Nat.cast_comm c v, Finite.Actions.GroupEndRing.hom_mul, Finite.Actions.GroupEndRing.hom_natCast]
  change A.torsionInclusion c ≫ (A.multiplication c ≫ v.hom A) = 1
  rw [← Category.assoc, A.comp_multiplication, A.torsionInclusion_pow, MonObj.one_comp]

include hc in
theorem existsUnique_groupEnd_division (p : Finite.Actions.GroupEndRing A)
    (hp : A.torsionInclusion c ≫ p.hom A = 1) :
    ∃! v : Finite.Actions.GroupEndRing A, (c : Finite.Actions.GroupEndRing A) * v = p := by
  obtain ⟨hf, he, hs⟩ := UnitMultiplication.unit_multiplication_finite_etale_surjective A.scheme c hc
  let q := A.multiplication c
  have : IsFinite q.left := hf
  have : Etale q.left := he
  have : Surjective q.left := hs
  have : IsMonHom q := by
    have h : IsMonHom ((c : Finite.Actions.GroupEndRing A).hom A) := inferInstance
    rw [Finite.Actions.GroupEndRing.hom_natCast] at h
    exact h
  have hk : ∀ (T : Over S) (x : T ⟶ A.scheme), x ≫ q = 1 → x ≫ p.hom A = 1 := by
    intro T x hx
    have hxc : x ^ c = 1 := (A.comp_multiplication c x).symm.trans hx
    let t := (A.torsionSchemePointsEquiv c T).symm ⟨x, hxc⟩
    have ht : t ≫ A.torsionInclusion c = x :=
      congrArg Subtype.val ((A.torsionSchemePointsEquiv c T).apply_symm_apply ⟨x, hxc⟩)
    rw [← ht, Category.assoc, hp, MonObj.comp_one]
  obtain ⟨v, ⟨hvgroup, hqv⟩, _⟩ := IsogenyFactorizationIs.IsogenyFactorization.fpqc_group_hom_descent q (p.hom A) hk
  let := hvgroup
  let r := Finite.Actions.GroupEndRing.ofHom A v
  have hr : (c : Finite.Actions.GroupEndRing A) * r = p := by
    rw [Nat.cast_comm c r]
    apply Finite.Actions.GroupEndRing.ext
    rw [Finite.Actions.GroupEndRing.hom_mul, Finite.Actions.GroupEndRing.hom_natCast]
    exact hqv
  refine ⟨r, hr, fun z hz => ?_⟩
  exact Finite.Actions.GroupEndRing.unit_natCast_mul_injective A c hc (hz.trans hr.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionDivision
