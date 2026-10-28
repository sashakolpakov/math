import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ConormalCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.GroupConormalNaturality

/-! # Conormal Lift Morphism Defect -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalLiftMorphismDefect

noncomputable section

/-! For an actual group morphism, discrepancies between two pairs of
local lifts differ by the coboundary of their original conormal defects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (C : Type) [CommRing C] [Algebra ℂ C] [Algebra.FiniteType ℂ C] [IsReduced C]

theorem conormalLiftMorphismDefect_coboundary
    (a₀ a₁ : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A)
    (b₀ b₁ : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ B)
    (ha : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ a₁ = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ a₀)
    (hb : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ b₁ = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ b₀)
    (h₀ : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ b₀ = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (a₀ ≫ f))
    (h₁ : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ b₁ = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (a₁ ≫ f)) :
    (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C a₀ ⟨a₁, ha⟩).comp (Intrinsic.GroupConormalMap.constructedConormalPullback f) -
        Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B C b₀ ⟨b₁, hb⟩ =
      Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B C (a₀ ≫ f) ⟨b₀, h₀⟩ -
        Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B C (a₁ ≫ f) ⟨b₁, h₁⟩ := by
  have haf : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (a₁ ≫ f) = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (a₀ ≫ f) := by
    rw [← Category.assoc, ha, Category.assoc]
  have hs := Regular.ConormalCocycle.regularConormalReference_cocycle B C (a₀ ≫ f) (a₁ ≫ f) b₁ haf h₁
  have ht := Regular.ConormalCocycle.regularConormalReference_cocycle B C (a₀ ≫ f) b₀ b₁ h₀ hb
  have hn := Regular.GroupConormalNaturality.regularGroupConormal_natural f C a₀ ⟨a₁, ha⟩
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact (congrArg (fun z => z + Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B C (a₁ ≫ f) ⟨b₁, h₁⟩) hn.symm).trans
    (hs.trans ht.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalLiftMorphismDefect
