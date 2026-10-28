import OAI.AlgebraicGeometry.AbelianVariety.CupDimensions
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Cup Unit Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupUnitNaturality

noncomputable section

/-! The genuine degree-zero cup unit is natural, and every degree-zero
class of the native abelian variety is a scalar multiple of that unit. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

theorem singularCohomologyPullback_cupUnit {R : Type} [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit Y) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X :=
  (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class (ModuleCat.of R R) f 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj Y))).trans
    (congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X 0)
      (Subtype.ext (AlgebraicTopology.Products.Cup.cupUnit_pullback (TopCat.toSSet.map f))))

theorem abelianH0_scalar (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : A.variety.rationalCohomology 0) :
    ∃ r : ℚ, a = r • AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (Betti.Scheme.schemePointSpace A.toOver) := by
  obtain ⟨x, rfl⟩ := (AbelianVariety.CupDimensions.Constructions.ExteriorCohomology.exteriorCup_zero_bijective A).surjective a
  exact ⟨exteriorPower.zeroEquiv ℚ _ x, AbelianVariety.CupDimensions.Constructions.ExteriorCohomology.exteriorCup_zero_formula A x⟩

theorem abelianH0_pullbacks_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {X : TopCat.{0}}
    (f g : X ⟶ Betti.Scheme.schemePointSpace A.toOver) (a : A.variety.rationalCohomology 0) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 0 a =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 0 a := by
  obtain ⟨r, rfl⟩ := abelianH0_scalar A a
  exact ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 0).hom.map_smul r _).trans
    ((congrArg (fun z => r • z) ((singularCohomologyPullback_cupUnit f).trans
      (singularCohomologyPullback_cupUnit g).symm)).trans
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 0).hom.map_smul r _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupUnitNaturality
