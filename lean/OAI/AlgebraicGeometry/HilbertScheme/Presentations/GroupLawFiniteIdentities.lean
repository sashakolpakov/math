import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Endomorphisms

/-! # Group Law Finite Identities -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroupLawFiniteIdentities.Core

noncomputable section

/-! The all-test-scheme group-law predicate is exactly two actual
morphism identities, with no representability hypothesis. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]
variable {T : Over S} (f : T ⨯ A ⟶ A)

def groupIdentityValue : T ⟶ A := prod.lift (𝟙 T) (1 : T ⟶ A) ≫ f

def groupProductValue : T ⨯ (A ⨯ A) ⟶ A :=
  prod.lift prod.fst ((prod.snd ≫ prod.fst) * (prod.snd ≫ prod.snd)) ≫ f

def productGroupValues : T ⨯ (A ⨯ A) ⟶ A :=
  (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ f) *
    (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f)

theorem preservesGroupLaw_iff_two_identities : Endomorphisms.Core.PreservesGroupLaw A f ↔
    groupIdentityValue A f = 1 ∧ groupProductValue A f = productGroupValues A f := by
  constructor
  · intro h
    exact ⟨(h T (𝟙 T)).1,
      (h (T ⨯ (A ⨯ A)) prod.fst).2 (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd)⟩
  · rintro ⟨hunit, hmul⟩ U t
    constructor
    · have h := congrArg (fun k => t ≫ k) hunit
      simpa only [groupIdentityValue, ← Category.assoc, prod.comp_lift, Category.comp_id,
        MonObj.comp_one] using h
    · intro x y
      have h := congrArg (fun k => prod.lift t (prod.lift x y) ≫ k) hmul
      simpa only [groupProductValue, productGroupValues, MonObj.comp_mul, prod.comp_lift,
        ← Category.assoc, prod.lift_fst, prod.lift_snd] using h

theorem preservesGroupLaw_iff_product_identity : Endomorphisms.Core.PreservesGroupLaw A f ↔
    groupProductValue A f = productGroupValues A f := by
  rw [preservesGroupLaw_iff_two_identities]
  refine ⟨And.right, fun hmul => ⟨?_, hmul⟩⟩
  have h := congrArg (fun k => prod.lift (𝟙 T) (prod.lift (1 : T ⟶ A) 1) ≫ k) hmul
  have hid : groupIdentityValue A f = groupIdentityValue A f * groupIdentityValue A f := by
    simpa only [groupProductValue, productGroupValues, groupIdentityValue, MonObj.comp_mul,
      prod.comp_lift, ← Category.assoc, prod.lift_fst, prod.lift_snd, one_mul] using h
  exact mul_eq_left.mp hid.symm

theorem groupProductValue_baseChange {U : Over S} (a : U ⟶ T) :
    groupProductValue A (prod.map a (𝟙 A) ≫ f) =
      prod.map a (𝟙 (A ⨯ A)) ≫ groupProductValue A f := by
  simp only [groupProductValue, ← Category.assoc, prod.lift_map, prod.comp_lift,
    MonObj.comp_mul, prod.map_fst, prod.map_snd, Category.comp_id]

theorem productGroupValues_baseChange {U : Over S} (a : U ⟶ T) :
    productGroupValues A (prod.map a (𝟙 A) ≫ f) =
      prod.map a (𝟙 (A ⨯ A)) ≫ productGroupValues A f := by
  simp only [productGroupValues, ← Category.assoc, prod.lift_map, prod.comp_lift,
    MonObj.comp_mul, prod.map_fst, prod.map_snd, Category.comp_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroupLawFiniteIdentities.Core
