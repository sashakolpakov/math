import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.RestrictedFactorization

/-! # Restricted -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Restricted.CechConeRestrictedComparison

noncomputable section

/-! The local factorization keeps the original resolution-coordinate
map and its subsequent comparison as two separate morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u a b c d e f g h
variable (C : Type u) [SemilatticeInf C] {ι : Type} [Finite ι]
  (U : ι → C) (V : C)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  {E : Type e} [Category.{f} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  {D : Type g} [Category.{h} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]
  (S : A ⥤ B) [S.Additive] (H : B ⥤ D) [H.Additive]
  (F : A ⥤ E) [F.Additive] (T : E ⥤ D) [T.Additive]
  (e : S ⋙ H ≅ F ⋙ T) (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (hF : ∀ W : C, IsIso ((F.mapHomologicalComplex (.up ℕ)).map
    (P.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)))
  (M : CochainComplex B ℕ)
  (η : (Functor.const Cᵒᵖ).obj M ⟶ TotalCoefficient.CechConeTotalCoefficient.mapped S P)

theorem comparison {K L : CochainComplex A ℕ}
    (c : K ≅ Total.CechConeTotal.total U P) (b : K ⟶ L) :
    (H.mapHomologicalComplex (.up ℕ)).map
        ((Realization.CechConeRealization.map S U P M η ≫ (S.mapHomologicalComplex (.up ℕ)).map c.inv) ≫
          (S.mapHomologicalComplex (.up ℕ)).map b) ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app L).hom =
    ((H.mapHomologicalComplex (.up ℕ)).map (η.app (op V)) ≫
        ((NatIso.mapHomologicalComplex e (.up ℕ)).app (P.obj (op V))).hom) ≫
      (T.mapHomologicalComplex (.up ℕ)).map
        ((Semilattice.MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P hF ≫
          (F.mapHomologicalComplex (.up ℕ)).map c.inv) ≫ (F.mapHomologicalComplex (.up ℕ)).map b) := by
  simpa only [Functor.map_comp, Category.assoc] using
    RestrictedFactorization.CechConeRestrictedFactorization.comparison C U V S H F T e P hF M η (c.inv ≫ b)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Restricted.CechConeRestrictedComparison
