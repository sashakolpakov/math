import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Injective Homology Ext -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt

noncomputable section

/-!
# The cohomology of an injective resolution computes derived morphisms

This module uses the actual cocycle constructor `InjectiveResolution.extMk`.
The kernel is proved to consist of boundaries, including degree zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite
open _root_.CochainComplex _root_.CochainComplex.HomComplex

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {R : Type t} [CommRing R] [Linear R C] {X Y : C} (I : InjectiveResolution Y)

theorem extMk_smul {n : ℕ} (f : X ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) (r : R) :
    I.extMk (r • f) (n + 1) rfl (by simp [hf]) =
      r • I.extMk f (n + 1) rfl hf := by
  have h := I.mk₀_comp_extMk f (n + 1) rfl hf (r • 𝟙 X)
  simpa only [Linear.smul_comp, Category.id_comp, Ext.mk₀_smul,
    Ext.smul_comp, Ext.mk₀_id_comp] using h.symm

theorem extMk_zero_degree_eq_zero_iff (f : X ⟶ I.cocomplex.X 0)
    (hf : f ≫ I.cocomplex.d 0 1 = 0) :
    I.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  simp only [← I.extEquivCohomologyClass.apply_eq_iff_eq,
    InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by norm_num)]
  have hz : IsZero (I.cochainComplex.X (-1)) :=
    CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by norm_num)
  constructor
  · rintro ⟨g, hg⟩
    have hg0 : g = 0 := hz.eq_of_tgt _ _
    rw [hg0, zero_comp] at hg
    apply (cancel_mono (I.cochainComplexXIso 0 0 rfl).inv).mp
    simpa only [zero_comp] using! hg.symm
  · intro h
    subst f
    exact ⟨0, by simp⟩

def homSectionsComplex (X : C) : CochainComplex (ModuleCat.{v} R) ℕ :=
  (((linearCoyoneda R C).obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

omit [HasExt C] in
theorem cocycle_condition (n : ℕ)
    (f : LinearMap.ker ((homSectionsComplex (R := R) I X).sc' (n - 1) n (n + 1)).g.hom) :
    f.val ≫ I.cocomplex.d n (n + 1) = 0 := f.property

def cocycleToExt (n : ℕ) :
    LinearMap.ker ((homSectionsComplex (R := R) I X).sc' (n - 1) n (n + 1)).g.hom →ₗ[R] Ext X Y n where
  toFun f := I.extMk f.val (n + 1) rfl (cocycle_condition I n f)
  map_add' f g := (I.add_extMk f.val g.val (n + 1) rfl
    (cocycle_condition I n f) (cocycle_condition I n g)).symm
  map_smul' r f := extMk_smul I f.val (cocycle_condition I n f) r

theorem cocycleToExt_surjective (n : ℕ) :
    Function.Surjective (cocycleToExt (R := R) (X := X) I n) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := I.extMk_surjective a (n + 1) rfl
  exact ⟨⟨f, hf⟩, hfa⟩

theorem cocycleToExt_kernel (n : ℕ) :
    LinearMap.ker (cocycleToExt (R := R) (X := X) I n) =
      LinearMap.range ((homSectionsComplex (R := R) I X).sc' (n - 1) n (n + 1)).moduleCatToCycles := by
  ext f
  change I.extMk f.val (n + 1) rfl (cocycle_condition I n f) = 0 ↔ _
  cases n with
  | zero =>
    erw [extMk_zero_degree_eq_zero_iff I]
    constructor
    · intro hf
      refine ⟨0, ?_⟩
      apply Subtype.ext
      rw [map_zero]
      exact hf.symm
    · rintro ⟨g, hg⟩
      have h := congrArg Subtype.val hg
      change g ≫ I.cocomplex.d 0 0 = f.val at h
      have hd : I.cocomplex.d 0 0 = 0 := I.cocomplex.shape _ _ (by simp)
      erw [hd, comp_zero] at h
      exact h.symm
  | succ n =>
    erw [I.extMk_eq_zero_iff _ _ _ _ n rfl]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      exact Subtype.ext hg
    · rintro ⟨g, hg⟩
      exact ⟨g, congrArg Subtype.val hg⟩

/-- The actual homology quotient is identified with the classes of resolution cocycles. -/
def homologyExtLinearEquiv (n : ℕ) :
    (homSectionsComplex (R := R) I X).homology n ≃ₗ[R] Ext X Y n := by
  let K := homSectionsComplex (R := R) I X
  have hp : (ComplexShape.up ℕ).prev n = n - 1 := by
    cases n <;> simp
  let e := (HomologicalComplex.homologyFunctorIso' (ModuleCat.{v} R) (ComplexShape.up ℕ)
    (n - 1) n (n + 1) hp (CochainComplex.next ℕ n)).app K
  exact e.toLinearEquiv.trans
    ((K.sc' (n - 1) n (n + 1)).moduleCatHomologyIso.toLinearEquiv.trans
      ((Submodule.quotEquivOfEq _ _ (cocycleToExt_kernel (R := R) (X := X) I n).symm).trans
        ((cocycleToExt (R := R) (X := X) I n).quotKerEquivOfSurjective
          (cocycleToExt_surjective I n))))

end

end OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt
