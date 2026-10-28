import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! # Opposite Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.OppositeComparison

noncomputable section

open _root_.ChainComplex
open _root_.CochainComplex
open _root_.ComplexShape

/-!
# Opposite categories of cochain complexes

We construct an equivalence of categories `CochainComplex.opEquivalence C`
between `(CochainComplex C ℤ)ᵒᵖ` and `CochainComplex Cᵒᵖ ℤ`, and we show
that two morphisms in `CochainComplex C ℤ` are homotopic iff they are
homotopic as morphisms in `CochainComplex Cᵒᵖ ℤ`.

-/

/- HilbertConstruction-local adaptation, using default elaboration settings. -/
set_option backward.isDefEq.respectTransparency false

open Opposite _root_.CategoryTheory Limits

variable (C : Type*) [Category* C]

namespace ComplexShape

/-- The embedding of the complex shape `up ℤ` in `down ℤ` given by `n ↦ -n`. -/
@[simps]
def embeddingUpIntDownInt : (up ℤ).Embedding (down ℤ) where
  f n := -n
  injective_f _ _ := by simp
  rel := by simp

instance : embeddingUpIntDownInt.IsRelIff where
  rel' := by
    intro i j h
    change -j + 1 = -i at h
    change i + 1 = j
    omega

/-- The embedding of the complex shape `down ℤ` in `up ℤ` given by `n ↦ -n`. -/
@[simps]
def embeddingDownIntUpInt : (down ℤ).Embedding (up ℤ) where
  f n := -n
  injective_f _ _ := by simp
  rel := by
    intro i j h
    change j + 1 = i at h
    change -i + 1 = -j
    omega

instance : embeddingDownIntUpInt.IsRelIff where
  rel' := by
    intro i j h
    change -i + 1 = -j at h
    change j + 1 = i
    omega

end ComplexShape

namespace ChainComplex

variable [HasZeroMorphisms C]

attribute [local simp] HomologicalComplex.XIsoOfEq in
/-- The equivalence of categories `ChainComplex C ℤ ≌ CochainComplex C ℤ`. -/
def cochainComplexEquivalence :
    ChainComplex C ℤ ≌ CochainComplex C ℤ where
  functor := ComplexShape.embeddingUpIntDownInt.restrictionFunctor C
  inverse := ComplexShape.embeddingDownIntUpInt.restrictionFunctor C
  unitIso :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ K.XIsoOfEq (by simp)) (by
        intro i j _
        change (K.XIsoOfEq (show i = - -i by omega)).hom ≫ K.d (- -i) (- -j) =
          K.d i j ≫ (K.XIsoOfEq (show j = - -j by omega)).hom
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d, HomologicalComplex.d_comp_XIsoOfEq_hom]))
      (by
        intro K L f
        ext n
        exact HomologicalComplex.XIsoOfEq_hom_naturality f (show n = - -n by omega))
  counitIso :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ K.XIsoOfEq (by simp)) (by
        intro i j _
        change (K.XIsoOfEq (neg_neg i)).hom ≫ K.d i j =
          K.d (- -i) (- -j) ≫ (K.XIsoOfEq (neg_neg j)).hom
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d, HomologicalComplex.d_comp_XIsoOfEq_hom]))
      (by
        intro K L f
        ext n
        exact HomologicalComplex.XIsoOfEq_hom_naturality f (neg_neg n))
  functor_unitIso_comp K := by
    apply HomologicalComplex.Hom.ext
    funext n
    change eqToHom (show K.X (-n) = K.X (- -(-n)) by congr 1; omega) ≫
      eqToHom (show K.X (- -(-n)) = K.X (-n) by congr 1; omega) = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]

end ChainComplex

namespace CochainComplex

open _root_.HomologicalComplex

/-- The equivalence of categories `(CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ`. -/
def opEquivalence [HasZeroMorphisms C] :
    (CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ :=
  (HomologicalComplex.opEquivalence C (.up ℤ)).trans
    (OppositeComparison.ChainComplex.cochainComplexEquivalence _)

variable {C} [Preadditive C]

@[local simp] private lemma opEquivalence_d (K : CochainComplex C ℤ) (i j : ℤ) :
    ((OppositeComparison.CochainComplex.opEquivalence C).functor.obj (op K)).d i j = (K.d (-j) (-i)).op := rfl

section

variable {K L : CochainComplex C ℤ} {f g : K ⟶ L}

/-- Negating the indices transports a chain homotopy to a cochain homotopy. -/
private def negRestrictionHomotopy {A B : ChainComplex C ℤ} {φ ψ : A ⟶ B}
    (h : Homotopy φ ψ) :
    Homotopy ((OppositeComparison.ChainComplex.cochainComplexEquivalence C).functor.map φ)
      ((OppositeComparison.ChainComplex.cochainComplexEquivalence C).functor.map ψ) where
  hom p q := h.hom (-p) (-q)
  zero p q hpq := h.zero (-p) (-q) (by
    change ¬(-p + 1 = -q)
    change ¬(q + 1 = p) at hpq
    omega)
  comm n := by
    rw [dNext_eq _ (i' := n + 1) (by rfl),
      prevD_eq _ (j' := n - 1) (by change n - 1 + 1 = n; omega)]
    change φ.f (-n) = A.d (-n) (-(n + 1)) ≫ h.hom (-(n + 1)) (-n) +
      h.hom (-n) (-(n - 1)) ≫ B.d (-(n - 1)) (-n) + ψ.f (-n)
    have hc := h.comm (-n)
    rw [dNext_eq _ (i' := -(n + 1)) (by change -(n + 1) + 1 = -n; omega),
      prevD_eq _ (j' := -(n - 1)) (by change -n + 1 = -(n - 1); omega)] at hc
    exact hc

/-- A homotopy of opposite cochain maps gives a homotopy of the original maps. -/
def homotopyUnop (h : Homotopy ((OppositeComparison.CochainComplex.opEquivalence C).functor.map f.op)
    ((OppositeComparison.CochainComplex.opEquivalence C).functor.map g.op)) : Homotopy f g := by
  let E := OppositeComparison.ChainComplex.cochainComplexEquivalence C
  let h' : Homotopy (E.inverse.map f) (E.inverse.map g) := h.unop
  have h'' := ((negRestrictionHomotopy h').compLeft (E.counitIso.inv.app K)).compRight
    (E.counitIso.hom.app L)
  have cancel (q : K ⟶ L) :
      (E.counitIso.inv.app K ≫ E.functor.map (E.inverse.map q)) ≫
        E.counitIso.hom.app L = q := by
    have hn : E.functor.map (E.inverse.map q) ≫ E.counitIso.hom.app L =
        E.counitIso.hom.app K ≫ q := E.counitIso.hom.naturality q
    calc
      _ = E.counitIso.inv.app K ≫ (E.counitIso.hom.app K ≫ q) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => E.counitIso.inv.app K ≫ k) hn)
      _ = q := by rw [← Category.assoc, E.counitIso.inv_hom_id_app K, Category.id_comp]
  exact cancel f ▸ cancel g ▸ h''

end

lemma exactAt_op {K : CochainComplex C ℤ} {n : ℤ} (hK : K.ExactAt n)
    (m : ℤ) (hm : n + m = 0 := by lia) :
    ((OppositeComparison.CochainComplex.opEquivalence C).functor.obj (op K)).ExactAt m := by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    ← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [_root_.CochainComplex.prev])
    (by grind [_root_.CochainComplex.next])] at hK

lemma acyclic_op {K : CochainComplex C ℤ} (hK : K.Acyclic) :
    ((OppositeComparison.CochainComplex.opEquivalence C).functor.obj (op K)).Acyclic :=
  fun n ↦ exactAt_op (hK (-n)) n

end CochainComplex

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.OppositeComparison
