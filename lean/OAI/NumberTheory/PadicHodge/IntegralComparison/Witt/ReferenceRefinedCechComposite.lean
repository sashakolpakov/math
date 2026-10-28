import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RefinedCechMapCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceCechComposite

/-! # Reference Refined Cech Composite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceRefinedCechComposite.Reference

noncomputable section

/-! The complete old-cover comparison in its original coefficient and
homology coordinates, before specializing the coefficient complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

universe s t
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (a : K ⟶ L)

omit [Fintype k] [CharP k p] in
theorem comparison (q : ℕ)
    {T S : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    {b b' : (RefinedCechMapCoordinates.total p k U L).homology q ⟶ T}
    {f : (RefinedCechMapCoordinates.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (RefinedCechMapCoordinates.map p k U a) q ≫ b)
    (hb : b = b')
    {c c' : S ⟶ (RefinedCechMapCoordinates.total p k U K).homology q}
    (hc : c = c') :
    c ≫ f = ReferenceCechComposite.Reference.composite.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U a q c' b' := by
  cases hb
  cases hc
  exact congrArg (fun m => c ≫ m) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.ReferenceRefinedCechComposite.Reference
