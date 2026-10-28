import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Tate Comparison Point Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

noncomputable section

/-! A name for TateComparison's literal raw point equation, retaining its component,
integral endomorphism, and full geometric neighbor multisets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def RawPointEquation {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : D.EndK)
    (i : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric i) : Prop :=
  D.endPoint f (D.aPoint hg i x - D.aPoint hg i y) =
    ((D.neighbors t b (x ≫ D.componentInclusion i)).map (D.aTotalPoint hg)).sum -
      ((D.neighbors t b (y ≫ D.componentInclusion i)).map (D.aTotalPoint hg)).sum

def RawAction (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : D.EndK) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (i : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric i),
    RawPointEquation D hg b t f i x y

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw
