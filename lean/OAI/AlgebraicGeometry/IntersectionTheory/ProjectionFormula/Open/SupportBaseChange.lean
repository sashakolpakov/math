import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.StalkSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ParameterQuotient

/-! # Support Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChange

noncomputable section

/-! Native reduced-support modules and their scalar quotients
commute with the actual stalk isomorphism of an open immersion. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable {Y X : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
  (A : IrreducibleCloseds Y) (B : IrreducibleCloseds X)
  (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint B)
  (y : Y) (hy : y ∈ (A : Set Y)) (hx : j y ∈ (B : Set X))

def equiv :
    letI : Algebra (X.presheaf.stalk (j y)) (Y.presheaf.stalk y) := (j.stalkMap y).hom.toAlgebra
    (Flat.Extension.baseChange (X.presheaf.stalk (j y)) (Y.presheaf.stalk y)).obj
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X B (j y) hx) ≃ₗ[Y.presheaf.stalk y] CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hy := by
  let R := X.presheaf.stalk (j y)
  let S := Y.presheaf.stalk y
  let : Algebra R S := (j.stalkMap y).hom.toAlgebra
  let p := Stalk.PrimeQuotient.kernelPrime X B (j y) hx
  let q := Stalk.PrimeQuotient.kernelPrime Y A y hy
  let eX := Stalk.PrimeQuotient.moduleEquiv X B (j y) hx p (Stalk.PrimeQuotient.kernelPrime_image X B (j y) hx)
  let eY := Stalk.PrimeQuotient.moduleEquiv Y A y hy q (Stalk.PrimeQuotient.kernelPrime_image Y A y hy)
  have hp : p.asIdeal.map (algebraMap R S) = q.asIdeal :=
    StalkSupport.kernelPrime_map j A B hA y hy hx
  exact ((Flat.Extension.baseChange R S).mapIso eX.toModuleIso).toLinearEquiv.trans
    ((Ideal.qoutMapEquivTensorQout (R := R) (I := p.asIdeal) S).symm.trans
      ((Submodule.quotEquivOfEq _ _ hp).trans eY.symm))

def quotientEquiv (r : X.presheaf.stalk (j y)) :
    letI : Algebra (X.presheaf.stalk (j y)) (Y.presheaf.stalk y) := (j.stalkMap y).hom.toAlgebra
    (Y.presheaf.stalk y) ⊗[X.presheaf.stalk (j y)]
      QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X B (j y) hx) ≃ₗ[Y.presheaf.stalk y]
        QuotSMulTop (j.stalkMap y r) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hy) := by
  let R := X.presheaf.stalk (j y)
  let S := Y.presheaf.stalk y
  let : Algebra R S := (j.stalkMap y).hom.toAlgebra
  exact ((Flat.ParameterQuotient.iso R S (CycleClass.Thom.IntersectionGeometry.localSupportModule X B (j y) hx) r).toLinearEquiv).trans
    (QuotSMulTop.congr (j.stalkMap y r) (equiv j A B hA y hy hx))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChange
