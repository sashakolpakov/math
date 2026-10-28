import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.DerivedRepresentatives
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Extended Acyclic Cocycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtendedAcyclicCocycles.Ext

noncomputable section

/-! Ext-acyclic nonnegative complexes retain acyclicity after extension by
zero. Their actual nonnegative cocycles represent all derived classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (K : CochainComplex C ℕ)

theorem extended_term_ext_vanish
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (i : ℤ) (q : ℕ) :
    Subsingleton (Ext A ((K.extend (ComplexShape.embeddingUpIntGE 0)).X i) (q + 1)) := by
  let H := (extFunctor.{w} (q + 1) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : H.Additive := inferInstanceAs ((extFunctorObj A (q + 1)).Additive)
  cases i with
  | ofNat n =>
    have : Subsingleton (H.obj (K.X n)) := hExt n q
    let e := H.mapIso (K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := n) (i' := (n : ℤ)) (by simp))
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton
  | negSucc n =>
    exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (K.extend (ComplexShape.embeddingUpIntGE 0))
        0 (Int.negSucc n) (by omega)))

omit [HasExt C] in
def extendedCocycle (n : ℕ) (f : A ⟶ K.X n) :
    A ⟶ (K.extend (ComplexShape.embeddingUpIntGE 0)).X (n : ℤ) :=
  f ≫ (K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := n) (by simp)).inv

omit [HasExt C] in
theorem extendedCocycle_closed (n : ℕ) (f : A ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0) :
    extendedCocycle A K n f ≫ (K.extend (ComplexShape.embeddingUpIntGE 0)).d
      (n : ℤ) ((n : ℤ) + 1) = 0 := by
  rw [K.extend_d_eq (ComplexShape.embeddingUpIntGE 0) (i := n) (j := n + 1) (by simp) (by simp)]
  change (f ≫ (K.extendXIso _ _).inv) ≫ (K.extendXIso _ _).hom ≫ _ = 0
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hf, zero_comp]

variable [EnoughInjectives C] [HasDerivedCategory.{w'} C]

theorem exists_nonnegative_derived_cocycle
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n : ℕ)
    (a : (DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj (K.extend (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧) :
    ∃ (f : A ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0),
      ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (extendedCocycle A K n f)
        (extendedCocycle_closed A K n f hf)) DerivedCategory.Q = a := by
  let e := ComplexShape.embeddingUpIntGE 0
  obtain ⟨g, hg, hga⟩ := Acyclic.DerivedRepresentatives.Ext.exists_derived_cocycle_representative A (K.extend e) 0
    (extended_term_ext_vanish A K hExt) (n : ℤ) a
  let f := g ≫ (K.extendXIso e (i := n) (i' := (n : ℤ)) (by simp [e])).hom
  have hf : f ≫ K.d n (n + 1) = 0 := by
    apply (cancel_mono (K.extendXIso e (i := n + 1) (i' := (n : ℤ) + 1) (by simp [e])).inv).mp
    change ((g ≫ (K.extendXIso e (i := n) (i' := (n : ℤ)) (by simp [e])).hom) ≫ K.d n (n + 1)) ≫ _ = _
    rw [Category.assoc, Category.assoc,
      ← K.extend_d_eq e (i := n) (j := n + 1) (by simp [e]) (by simp [e]), hg, zero_comp]
  have he : extendedCocycle A K n f = g := by
    change (g ≫ (K.extendXIso e _).hom) ≫ (K.extendXIso e _).inv = g
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨f, hf, ?_⟩
  simpa only [he] using hga

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtendedAcyclicCocycles.Ext
