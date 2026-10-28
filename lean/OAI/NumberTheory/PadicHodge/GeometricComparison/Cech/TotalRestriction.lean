import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient

/-! # Total Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestriction.CechTotalRestrictionComparison

noncomputable section

/-! Restriction compatible with sheafification identifies the original
restricted Čech total with the sheafified restricted coefficient total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a b c d e f g h
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type c} [Category.{d} B] [Preadditive B]
  {E : Type e} [Category.{f} E] [Abelian E] [HasProducts.{0} E] [HasCoproducts.{0} E]
  {D : Type g} [Category.{h} D] [Preadditive D]
  (S : A ⥤ B) [S.Additive] (R : B ⥤ D) [R.Additive]
  (T : A ⥤ E) [T.Additive] (L : E ⥤ D) [L.Additive]
  (e : S ⋙ R ≅ T ⋙ L) {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ)

def iso : (R.mapHomologicalComplex (.up ℕ)).obj
      ((S.mapHomologicalComplex (.up ℕ)).obj (CechCone.Total.CechConeTotal.total U P)) ≅
    (L.mapHomologicalComplex (.up ℕ)).obj
      (CechCone.Total.CechConeTotal.total U (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped T P)) :=
  (NatIso.mapHomologicalComplex e (.up ℕ)).app (CechCone.Total.CechConeTotal.total U P) ≪≫
    (L.mapHomologicalComplex (.up ℕ)).mapIso (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso T U P)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalRestriction.CechTotalRestrictionComparison
