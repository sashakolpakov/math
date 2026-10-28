import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityIdeal

/-! # Proper Equation Ideals -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationIdeals

noncomputable section

/-! Finite lists of actual morphism equations from proper flat sources have a single defining ideal with exact tests after arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure ProperFamilyMorphismEquation (S : Scheme.{u}) where
  source : Over S
  target : Over S
  proper : IsProper source.hom
  flat : Flat source.hom
  separated : IsSeparated target.hom
  lhs : source ⟶ target
  rhs : source ⟶ target

attribute [instance] ProperFamilyMorphismEquation.proper ProperFamilyMorphismEquation.flat
  ProperFamilyMorphismEquation.separated

def ProperFamilyMorphismEquation.ideal {S : Scheme.{u}} [IsLocallyNoetherian S]
    (e : ProperFamilyMorphismEquation S) : S.IdealSheafData := Proper.MorphismEqualityIdeal.properMorphismEqualityIdeal e.lhs e.rhs

theorem ProperFamilyMorphismEquation.ideal_test {S T : Scheme.{u}} [IsLocallyNoetherian S]
    (e : ProperFamilyMorphismEquation S) (c : T ⟶ S) :
    e.ideal.comap c = ⊥ ↔ (Over.pullback c).map e.lhs = (Over.pullback c).map e.rhs :=
  Proper.MorphismEqualityIdeal.properMorphismEqualityIdeal_test e.lhs e.rhs c

def properEquationListIdeal {S : Scheme.{u}} [IsLocallyNoetherian S]
    (R : List (ProperFamilyMorphismEquation S)) : S.IdealSheafData :=
  R.foldr (fun e I => e.ideal ⊔ I) ⊥

theorem properEquationListIdeal_test {S T : Scheme.{u}} [IsLocallyNoetherian S]
    (R : List (ProperFamilyMorphismEquation S)) (c : T ⟶ S) :
    (properEquationListIdeal R).comap c = ⊥ ↔
      ∀ e ∈ R, (Over.pullback c).map e.lhs = (Over.pullback c).map e.rhs := by
  induction R with
  | nil => simp [properEquationListIdeal]
  | cons e R ih =>
      change (e.ideal ⊔ properEquationListIdeal R).comap c = ⊥ ↔ _
      rw [Scheme.IdealSheafData.comap_sup, sup_eq_bot_iff, e.ideal_test c, ih, List.forall_mem_cons]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperEquationIdeals
