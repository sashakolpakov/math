import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.NatIsoLocalNaturality

/-! # Homology Local -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyLocal.Comparison

noncomputable section

/-! A local comparison on actual evaluated complexes induces the corresponding original homology-presheaf map. -/

open _root_.CategoryTheory

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  (K L : CochainComplex (C ⥤ A) ℕ) (n : ℕ)

def map (c : C) (a : (HomologicalComplex.asFunctor K).obj c ⟶ (HomologicalComplex.asFunctor L).obj c) :
    (K.homology n).obj c ⟶ (L.homology n).obj c :=
  (HomologyEvaluation.component K n c).inv ≫ HomologicalComplex.homologyMap a n ≫
    (HomologyEvaluation.component L n c).hom

theorem naturality {c d : C} (f : c ⟶ d)
    (a : (HomologicalComplex.asFunctor K).obj c ⟶ (HomologicalComplex.asFunctor L).obj c)
    (b : (HomologicalComplex.asFunctor K).obj d ⟶ (HomologicalComplex.asFunctor L).obj d)
    (h : HomologicalComplex.homologyMap (a ≫ (HomologicalComplex.asFunctor L).map f) n =
      HomologicalComplex.homologyMap ((HomologicalComplex.asFunctor K).map f ≫ b) n) :
    (K.homology n).map f ≫ Comparison.map K L n d b = Comparison.map K L n c a ≫ (L.homology n).map f := by
  let H := HomologicalComplex.homologyFunctor A (.up ℕ) n
  have hh : H.map ((HomologicalComplex.asFunctor K).map f) ≫ H.map b =
      H.map a ≫ H.map ((HomologicalComplex.asFunctor L).map f) :=
    (H.map_comp _ _).symm.trans (h.symm.trans (H.map_comp _ _))
  have hs := NatIsoLocalNaturality.square (HomologyEvaluation.iso K n)
    (HomologyEvaluation.iso L n) f (H.map a) (H.map b) hh
  exact hs.trans
    ((congrArg (fun t => (HomologyEvaluation.component K n c).inv ≫ t)
      (Category.assoc _ _ ((L.homology n).map f)).symm).trans (Category.assoc _ _ _).symm)

instance map_isIso (c : C)
    (a : (HomologicalComplex.asFunctor K).obj c ⟶ (HomologicalComplex.asFunctor L).obj c)
    [QuasiIsoAt a n] : IsIso (Comparison.map K L n c a) := by
  dsimp only [Comparison.map]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologyLocal.Comparison
