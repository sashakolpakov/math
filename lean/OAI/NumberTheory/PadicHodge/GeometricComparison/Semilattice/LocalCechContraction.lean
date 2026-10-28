import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechContraction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MeetRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChange

/-! # Local Cech Contraction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechContraction.SemilatticeLocalCechContraction

noncomputable section

/-! If coefficient restriction to intersection with one chart is invertible,
the original Čech cochain complex contracts to its coefficient on that chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u w v z
variable (C : Type u) [SemilatticeInf C] {ι : Type w} (U : ι → C) (i : ι)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op))

def family : ι → Set.Iic (U i) := (MeetRestriction.SemilatticeMeetRestriction.restriction C (U i)).obj ∘ U

theorem family_self : family C U i i = ⊤ := by
  apply Subtype.ext
  change U i ⊓ U i = U i
  exact inf_idem (U i)

def coefficients : (Set.Iic (U i))ᵒᵖ ⥤ A := (MeetRestriction.SemilatticeMeetRestriction.inclusion C (U i)).op ⋙ P

def complexIso : (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P ≅
    (IntegralComparison.NonemptyCechNerve.complexFunctor (family C U i)).obj (coefficients C U i P) :=
  (IntegralComparison.NonemptyCechNerve.complexFunctor U).mapIso (MeetRestriction.SemilatticeMeetRestriction.iso C (U i) P h) ≪≫
    NonemptyCech.BaseChange.NonemptyCechBaseChange.complexIso (MeetRestriction.SemilatticeMeetRestriction.restriction C (U i)) U
      (coefficients C U i P)

def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ A).obj (P.obj (op (U i))))
    ((IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P) :=
  (CechContraction.SemilatticeCechContraction.homotopyEquiv (Set.Iic (U i)) (family C U i) i
    (family_self C U i) (coefficients C U i P)).trans
      (HomotopyEquiv.ofIso (complexIso C U i P h).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechContraction.SemilatticeLocalCechContraction
