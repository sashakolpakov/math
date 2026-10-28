import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Nat Extended Acyclic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.NatExtendedAcyclic

noncomputable section

/-! # Extension by zero preserves termwise acyclicity and monomorphisms -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

set_option backward.isDefEq.respectTransparency false in
/-- The literal nonnegative embedding used by the original complexes preserves higher Ext vanishing. -/
theorem natExtended_term_ext_vanish (A : C) (K : CochainComplex C ℕ)
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (i : ℤ) (q : ℕ) :
    Subsingleton (Ext A ((K.extend ComplexShape.embeddingUpNat).X i) (q + 1)) := by
  let H := (extFunctor.{w} (q + 1) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : H.Additive := inferInstanceAs ((extFunctorObj A (q + 1)).Additive)
  cases i with
  | ofNat n =>
    have : Subsingleton (H.obj (K.X n)) := hExt n q
    let e := H.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton
  | negSucc n =>
    exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero
      (K.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n) (by
        intro i hi
        change (i : ℤ) = Int.negSucc n at hi
        omega)))

set_option backward.isDefEq.respectTransparency false in
omit [HasExt C] in
/-- The actual extended inclusion is monic in every degree. -/
theorem natExtended_map_f_mono {K L : CochainComplex C ℕ} (f : K ⟶ L)
    [∀ i, Mono (f.f i)] (i : ℤ) :
    Mono ((HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f i) := by
  cases i with
  | ofNat n =>
    change Mono ((HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f (n : ℤ))
    rw [HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
    infer_instance
  | negSucc n =>
    exact (K.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n) (by
      intro i hi
      change (i : ℤ) = Int.negSucc n at hi
      omega)).mono _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.NatExtendedAcyclic
