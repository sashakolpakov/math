import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

/-! # Sheaf Complex Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift.Constructions

noncomputable section

/-! Lift actual presheaf cochain maps to sheaf complexes by sheafification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}
variable {K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ}
variable {L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}

def sheafComplexLift (f : K ⟶ AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex L) :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex K ⟶ L where
  f n := ⟨CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) (f.f n) (L.X n).property⟩
  comm' i j _ := by
    apply Sheaf.hom_ext
    symm
    change CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (K.d i j) ≫
        CategoryTheory.sheafifyLift _ (f.f j) (L.X j).property =
      CategoryTheory.sheafifyLift _ (f.f i) (L.X i).property ≫ (L.d i j).hom
    rw [CategoryTheory.sheafifyMap_sheafifyLift,
      ← CategoryTheory.sheafifyLift_comp]
    exact congrArg (fun h => CategoryTheory.sheafifyLift
      (Opens.grothendieckTopology X) h (L.X j).property) (f.comm i j).symm

theorem sheafComplexLift_unit (f : K ⟶ AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex L) (n : ℕ) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n) ≫
        ((sheafComplexLift f).f n).hom = f.f n :=
  CategoryTheory.toSheafify_sheafifyLift _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift.Constructions
