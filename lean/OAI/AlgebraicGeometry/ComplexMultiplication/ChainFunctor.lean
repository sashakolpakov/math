import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Homology.Additive

/-! # Chain Functor -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ChainFunctor

noncomputable section

/-! # Simplicial chains commute with additive functors preserving coproducts -/

open _root_.CategoryTheory Limits
open scoped Simplicial

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F]
  (S : SSet.{0}) (R : C)

/-- The degreewise coproduct comparison for simplicial chains. -/
def chainFunctorXIso (n : ℕ) :
    F.obj ((S.chainComplex R).X n) ≅ (S.chainComplex (F.obj R)).X n :=
  (asIso (sigmaComparison F (fun _ : S _⦋n⦌ ↦ R))).symm

@[reassoc]
theorem iota_chainFunctorXIso_inv {n : ℕ} (x : S _⦋n⦌) :
    S.ιChainComplex (R := F.obj R) x ≫ (chainFunctorXIso F S R n).inv =
      F.map (S.ιChainComplex (R := R) x) :=
  ι_comp_sigmaComparison F (fun _ : S _⦋n⦌ ↦ R) x

@[reassoc]
theorem map_iota_chainFunctorXIso_hom {n : ℕ} (x : S _⦋n⦌) :
    F.map (S.ιChainComplex (R := R) x) ≫ (chainFunctorXIso F S R n).hom =
      S.ιChainComplex (R := F.obj R) x :=
  map_ι_comp_inv_sigmaComparison F (fun _ : S _⦋n⦌ ↦ R) x

variable [F.Additive]

/-- Applying an additive coproduct-preserving functor before or after forming simplicial
chains gives canonically isomorphic chain complexes, with the original alternating boundary. -/
def chainFunctorIso :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (S.chainComplex R) ≅
      S.chainComplex (F.obj R) :=
  HomologicalComplex.Hom.isoOfComponents (chainFunctorXIso F S R) (by
    intro i j hij
    obtain rfl := hij
    apply (cancel_epi (chainFunctorXIso F S R (j + 1)).inv).1
    apply SSet.chainComplex_hom_ext
    intro x
    change S.ιChainComplex x ≫ (chainFunctorXIso F S R (j + 1)).inv ≫
        (chainFunctorXIso F S R (j + 1)).hom ≫ (S.chainComplex (F.obj R)).d (j + 1) j =
      S.ιChainComplex x ≫ (chainFunctorXIso F S R (j + 1)).inv ≫
        F.map ((S.chainComplex R).d (j + 1) j) ≫ (chainFunctorXIso F S R j).hom
    calc
      _ = S.ιChainComplex x ≫ (S.chainComplex (F.obj R)).d (j + 1) j := by simp
      _ = ∑ k : Fin (j + 2), (-1) ^ k.val • S.ιChainComplex (S.δ k x) :=
        SSet.ιChainComplex_d S (F.obj R) x
      _ = (∑ k : Fin (j + 2), (-1) ^ k.val •
          F.map (S.ιChainComplex (R := R) (S.δ k x))) ≫
            (chainFunctorXIso F S R j).hom := by
        simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
          map_iota_chainFunctorXIso_hom]
      _ = F.map (S.ιChainComplex (R := R) x ≫ (S.chainComplex R).d (j + 1) j) ≫
          (chainFunctorXIso F S R j).hom := by
        rw [SSet.ιChainComplex_d, Functor.map_sum]
        simp only [Functor.map_zsmul]
      _ = _ := by rw [Functor.map_comp, ← iota_chainFunctorXIso_inv]; simp only [Category.assoc])

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ChainFunctor
