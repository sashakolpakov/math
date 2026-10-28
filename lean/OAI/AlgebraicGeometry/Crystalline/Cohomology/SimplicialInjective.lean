import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Simplicial Injective -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SimplicialInjective.SimplicialInjectiveHom

noncomputable section

/-!
# Injective duals of exact simplicial chains

The coface differential on morphisms into an injective object is
precomposition with the original face differential. Exactness of the
chain complex therefore extends every cocycle across the next image,
giving a boundary in the dual cochain complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial _root_.AlgebraicTopology

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (Y : SimplicialObject C) (I : C)

def cosimplicial : CosimplicialObject AddCommGrpCat.{v} :=
  Y.rightOp ⋙ preadditiveYoneda.obj I

def complex : CochainComplex AddCommGrpCat.{v} ℕ :=
  AlternatingCofaceMapComplex.obj (cosimplicial Y I)

theorem differential_apply (n : ℕ) (a : Y.obj (op ⦋n⦌) ⟶ I) :
    (complex Y I).d n (n + 1) a = (AlternatingFaceMapComplex.obj Y).d (n + 1) n ≫ a := by
  let H := cosimplicial Y I
  let ev : (H.obj ⦋n⦌ ⟶ H.obj ⦋n + 1⦌) →+ (Y.obj (op ⦋n + 1⦌) ⟶ I) :=
    { toFun f := f a
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hsum : AlternatingCofaceMapComplex.objD H n a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Y.δ i ≫ a) := by
    change ev (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • H.δ i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_zsmul ev ((-1 : ℤ) ^ (i : ℕ)) (H.δ i)
  have hcomp : AlternatingFaceMapComplex.objD Y n ≫ a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Y.δ i ≫ a) :=
    (Preadditive.sum_comp Finset.univ (fun i : Fin (n + 2) => (-1 : ℤ) ^ (i : ℕ) • Y.δ i) a).trans
      (Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp (Y.δ i) a ((-1 : ℤ) ^ (i : ℕ))))
  have hc : (complex Y I).d n (n + 1) = AlternatingCofaceMapComplex.objD H n :=
    CochainComplex.of_d (fun i => H.obj ⦋i⦌) (AlternatingCofaceMapComplex.objD H) n
  have hd : (AlternatingFaceMapComplex.obj Y).d (n + 1) n = AlternatingFaceMapComplex.objD Y n :=
    ChainComplex.of_d (fun i => Y.obj (op ⦋i⦌)) (AlternatingFaceMapComplex.objD Y) n
  exact (congrArg (fun f => f a) hc).trans
    (hsum.trans (hcomp.symm.trans (congrArg (fun f => f ≫ a) hd).symm))

theorem exactAt [Injective I] (n : ℕ) (hY : (AlternatingFaceMapComplex.obj Y).ExactAt (n + 1)) :
    (complex Y I).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rw [ShortComplex.ab_exact_iff]
  intro a ha
  change Y.obj (op ⦋n + 1⦌) ⟶ I at a
  have hS : ((AlternatingFaceMapComplex.obj Y).sc' (n + 2) (n + 1) n).Exact :=
    (HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)).mp hY
  have hz : (AlternatingFaceMapComplex.obj Y).d (n + 2) (n + 1) ≫ a = 0 :=
    (differential_apply Y I (n + 1) a).symm.trans ha
  refine ⟨hS.descToInjective a hz, ?_⟩
  exact (differential_apply Y I n (hS.descToInjective a hz)).trans
    (hS.comp_descToInjective a hz)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SimplicialInjective.SimplicialInjectiveHom
