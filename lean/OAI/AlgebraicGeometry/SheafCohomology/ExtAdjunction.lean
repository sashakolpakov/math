import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Ext Adjunction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ExtAdjunction.Projective

noncomputable section

/-! Comparison of Ext under an exact right adjoint, for the coefficient
comparison needed by ProjectiveCohomology's coherent cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
variable (X : C) (X₀ : D) (a : X ⟶ G.obj X₀)

/-- Apply an exact functor, then pull the source back along `a`. -/
def extCompare (Y : D) (n : ℕ) : Ext X₀ Y n →+ Ext X (G.obj Y) n :=
  ((Ext.mk₀ a).precomp (G.obj Y) (Nat.zero_add n)).comp (G.mapExtAddHom X₀ Y n)

@[simp] theorem extCompare_apply (Y : D) (n : ℕ) (x : Ext X₀ Y n) :
    extCompare G X X₀ a Y n x =
      (Ext.mk₀ a).comp (x.mapExactFunctor G) (Nat.zero_add n) := rfl

@[simp] theorem extCompare_mk₀ {Y : D} (f : X₀ ⟶ Y) :
    extCompare G X X₀ a Y 0 (Ext.mk₀ f) = Ext.mk₀ (a ≫ G.map f) := by
  simp only [extCompare_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- Exact functors preserving injectives extend a natural Hom comparison
to all Ext degrees. -/
theorem extCompare_bijective [EnoughInjectives D] [G.PreservesInjectiveObjects]
    (h₀ : ∀ Y : D, Function.Bijective (fun f : X₀ ⟶ Y => a ≫ G.map f))
    (Y : D) (n : ℕ) : Function.Bijective (extCompare G X X₀ a Y n) := by
  induction n generalizing Y with
  | zero =>
      have he : (extCompare G X X₀ a Y 0 : Ext X₀ Y 0 → Ext X (G.obj Y) 0) =
          Ext.homEquiv₀.symm ∘ (fun f => a ≫ G.map f) ∘ Ext.homEquiv₀ := by
        funext x
        change extCompare G X X₀ a Y 0 x = Ext.mk₀ (a ≫ G.map (Ext.homEquiv₀ x))
        rw [← extCompare_mk₀, Ext.mk₀_homEquiv₀_apply]
      rw [he]
      exact Ext.homEquiv₀.symm.bijective.comp ((h₀ Y).comp Ext.homEquiv₀.bijective)
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := ShortComplex.mk _ _ (cokernel.condition I.f)
      have : Injective S.X₂ := I.injective
      have : Injective (S.map G).X₂ :=
        Functor.PreservesInjectiveObjects.injective_obj I.injective
      have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact I.f }
      have hSD := hS.map G
      apply AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
        ((Ext.mk₀ S.g).postcomp X₀ (Nat.add_zero n))
        (hS.extClass.postcomp X₀ (rfl : n + 1 = n + 1))
        ((Ext.mk₀ (G.map S.g)).postcomp X (Nat.add_zero n))
        (hSD.extClass.postcomp X (rfl : n + 1 = n + 1))
        (extCompare G X X₀ a S.X₂ n) (extCompare G X X₀ a S.X₃ n)
        (extCompare G X X₀ a S.X₁ (n + 1))
      · ext x
        change ((Ext.mk₀ a).comp (x.mapExactFunctor G) (Nat.zero_add n)).comp
          (Ext.mk₀ (G.map S.g)) (Nat.add_zero n) =
          (Ext.mk₀ a).comp ((x.comp (Ext.mk₀ S.g) (Nat.add_zero n)).mapExactFunctor G)
            (Nat.zero_add n)
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
          Ext.comp_assoc_of_third_deg_zero]
      · ext x
        change ((Ext.mk₀ a).comp (x.mapExactFunctor G) (Nat.zero_add n)).comp
          hSD.extClass rfl =
          (Ext.mk₀ a).comp ((x.comp hS.extClass rfl).mapExactFunctor G)
            (Nat.zero_add (n + 1))
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
        exact Ext.comp_assoc _ _ _ (Nat.zero_add n) rfl (by omega)
      · exact (ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' X₀ hS n (n + 1) rfl)
      · exact (ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' X hSD n (n + 1) rfl)
      · exact (hn _).surjective
      · exact hn _
      · intro x
        exact Ext.covariant_sequence_exact₁ _ hS x
          (by exact @Subsingleton.elim _ (Ext.subsingleton_of_injective _ _ n) _ _) rfl
      · intro x
        exact Ext.covariant_sequence_exact₁ _ hSD x
          (by exact @Subsingleton.elim _ (Ext.subsingleton_of_injective _ _ n) _ _) rfl

/-- An exact right adjoint has the expected Ext adjunction when its left
adjoint preserves monomorphisms. This is an equivalence of the actual Ext groups. -/
def extAdjunction [EnoughInjectives D] {F : C ⥤ D} [F.PreservesMonomorphisms]
    (adj : F ⊣ G) (Y : D) (n : ℕ) : Ext (F.obj X) Y n ≃+ Ext X (G.obj Y) n := by
  have : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  exact AddEquiv.ofBijective (extCompare G X (F.obj X) (adj.unit.app X) Y n)
    (extCompare_bijective G X (F.obj X) (adj.unit.app X)
      (fun Z => (adj.homEquiv X Z).bijective) Y n)

end

end OAI.AlgebraicGeometry.SheafCohomology.ExtAdjunction.Projective
