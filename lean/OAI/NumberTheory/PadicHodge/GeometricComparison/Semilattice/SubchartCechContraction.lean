import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechContraction

/-! # Subchart Cech Contraction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartCechContraction.SemilatticeSubchartCechContraction

noncomputable section

/-! The actual Čech contraction also applies on any subchart contained
in one member of the indexing family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u w v z
variable (C : Type u) [SemilatticeInf C] {ι : Type w} (U : ι → C) (I : C)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def family : ι → Set.Iic I := (MeetRestriction.SemilatticeMeetRestriction.restriction C I).obj ∘ U

theorem family_self (i : ι) (hi : I ≤ U i) : family C U I i = ⊤ := by
  apply Subtype.ext
  change U i ⊓ I = I
  exact inf_eq_right.mpr hi

def coefficients : (Set.Iic I)ᵒᵖ ⥤ A := (MeetRestriction.SemilatticeMeetRestriction.inclusion C I).op ⋙ P

def complexIso : (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P ≅
    (IntegralComparison.NonemptyCechNerve.complexFunctor (family C U I)).obj (coefficients C I P) :=
  (IntegralComparison.NonemptyCechNerve.complexFunctor U).mapIso (MeetRestriction.SemilatticeMeetRestriction.iso C I P h) ≪≫
    NonemptyCech.BaseChange.NonemptyCechBaseChange.complexIso (MeetRestriction.SemilatticeMeetRestriction.restriction C I) U (coefficients C I P)

def homotopyEquiv (i : ι) (hi : I ≤ U i) :
    HomotopyEquiv ((CochainComplex.single₀ A).obj (P.obj (op I)))
      ((IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P) :=
  (CechContraction.SemilatticeCechContraction.homotopyEquiv (Set.Iic I) (family C U I) i
    (family_self C U I i hi) (coefficients C I P)).trans
      (HomotopyEquiv.ofIso (complexIso C U I P h).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartCechContraction.SemilatticeSubchartCechContraction
