import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TestBaseChangePoints

/-! # Base Change Test Lifting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChangeTestLifting.Construction

noncomputable section

/-! Every further test over a source restriction is itself a test over
the new base. This retains the original scheme, including its nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S S' : Scheme} (s : S' ⟶ S) {Q : Over S'} {U : Over S}
variable (t : U ⟶ (Over.map s).obj Q)

def liftedBaseChangeTest : Over S' := Over.mk (t.left ≫ Q.hom)

def liftedBaseChangeTestMap : liftedBaseChangeTest s t ⟶ Q := Over.homMk t.left

def liftedBaseChangeTestIso : (Over.map s).obj (liftedBaseChangeTest s t) ≅ U :=
  Over.isoMk (Iso.refl U.left) (by
    change (𝟙 U.left) ≫ U.hom = (t.left ≫ Q.hom) ≫ s
    rw [Category.id_comp, Category.assoc]
    exact t.w.symm)

theorem liftedBaseChangeTestMap_square :
    (Over.map s).map (liftedBaseChangeTestMap s t) = (liftedBaseChangeTestIso s t).hom ≫ t := by
  apply Over.OverMorphism.ext
  exact (Category.id_comp t.left).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChangeTestLifting.Construction
