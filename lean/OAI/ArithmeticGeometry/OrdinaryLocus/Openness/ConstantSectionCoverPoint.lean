import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCoordinates
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf

/-! # Constant Section Cover Point -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantSectionCoverPoint.Construction

noncomputable section

/-! A constant section is contained in one member of a finite affine section cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

universe u

theorem exists_constantSection_cover_index
    {K : Type u} [Field K] (A S : Over (Spec (.of K)))
    (D : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data A.left) (s : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    ∃ i : D.I, ⊤ ≤ (ConstantProductCoordinates.Construction.constantFamilySection A S s).left ⁻¹ᵁ
      ((fst A S).left ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (D.sectionHom i)) := by
  have : Subsingleton (𝟙_ (Over (Spec (.of K)))).left := inferInstanceAs (Subsingleton (Spec (.of K)))
  obtain ⟨i, hi⟩ := D.covers (s.left (IsLocalRing.closedPoint K))
  refine ⟨i, ?_⟩
  intro x hx
  have he := congrArg (fun f : S.left ⟶ A.left ↦ f x)
    (congrArg Over.Hom.left (ConstantProductCoordinates.Construction.constantFamilySection_factor A S s))
  have ht : (toUnit S).left x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hval := he.trans (congrArg s.left ht)
  exact (congrArg (fun y : A.left ↦ y ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (D.sectionHom i)) hval).mpr hi

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantSectionCoverPoint.Construction
