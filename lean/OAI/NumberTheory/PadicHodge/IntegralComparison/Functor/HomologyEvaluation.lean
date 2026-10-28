import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Homology Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyEvaluation

noncomputable section

/-! Original homology of a functor-valued complex is its pointwise homology, naturally in the index. -/

open _root_.CategoryTheory

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  (K : CochainComplex (C ⥤ A) ℕ) (n : ℕ)

def component (c : C) : ((HomologicalComplex.asFunctor K).obj c).homology n ≅
    (K.homology n).obj c :=
  (K.sc n).mapHomologyIso ((evaluation C A).obj c)

theorem naturality {c d : C} (a : c ⟶ d) :
    (component K n c).hom ≫ (K.homology n).map a =
      HomologicalComplex.homologyMap ((HomologicalComplex.asFunctor K).map a) n ≫
        (component K n d).hom := by
  let S := K.sc n
  let τ := (evaluation C A).map a
  have h := S.homologyMap_mapNatTrans τ
  change (S.mapHomologyIso ((evaluation C A).obj c)).hom ≫ τ.app S.homology =
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso ((evaluation C A).obj d)).hom
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

def iso : HomologicalComplex.asFunctor K ⋙ HomologicalComplex.homologyFunctor A (.up ℕ) n ≅
    K.homology n :=
  NatIso.ofComponents (component K n) (by
    intro c d a
    exact (naturality K n a).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyEvaluation
