import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportNaturality

/-! # Relative Top Support Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions

noncomputable section

/-! Passing from the top open to the original space respects actual relative support inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0})

def relativeComplementChange {A B : Set X} (h : A ⊆ B) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B ⟶ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => h hx)

variable {C D : Opens X} (h : C ≤ D)

theorem relativeCochainPresheafTopIso_support_naturality :
    IntersectSupportNaturality.Constructions.relativeOpenComplementChange h ⊤ ≫ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X (C : Set X)).hom =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X (D : Set X)).hom ≫
        relativeComplementChange X h := by
  dsimp only [IntersectSupportNaturality.Constructions.relativeOpenComplementChange, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso, relativeComplementChange]
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp]
  congr 1

theorem relativeCohomologyPresheafTopIso_support_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (IntersectSupportNaturality.Constructions.relativeOpenComplementChange h ⊤) n ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X (C : Set X) n).hom =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X (D : Set X) n).hom ≫
        HomologicalComplex.homologyMap (relativeComplementChange X h) n := by
  change HomologicalComplex.homologyMap (IntersectSupportNaturality.Constructions.relativeOpenComplementChange h ⊤) n ≫
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X (C : Set X)).hom n =
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X (D : Set X)).hom n ≫
      HomologicalComplex.homologyMap (relativeComplementChange X h) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeCochainPresheafTopIso_support_naturality]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions
