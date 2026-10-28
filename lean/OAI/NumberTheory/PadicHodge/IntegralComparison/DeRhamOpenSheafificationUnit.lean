import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSheafificationUnit

/-! # De Rham Open Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamOpenSheafificationUnit

noncomputable section

/-! The original de Rham sheafification unit is compatible with actual open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] (X Y : Over (Spec (CommRingCat.of k)))
  (g : X.left ⟶ Y.left) [IsOpenImmersion g] (hg : g ≫ Y.hom = X.hom)

def formsIso (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n ≅
    g.opensFunctor.op ⋙ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k Y n :=
  Functor.isoWhiskerRight (Open.SectionAlgebraIso.iso k X Y g hg) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n) ≪≫
    Functor.associator g.opensFunctor.op (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsFunctor n)

include hg in
theorem isIso (n : ℕ) (U : X.left.Opens)
    [IsIso ((toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app (op U))] :
    IsIso ((toSheafify (Opens.grothendieckTopology Y.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k Y n)).app
      (op (g ''ᵁ U))) := by
  let : IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (g.opensFunctor.op ⋙ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k Y n)).app (op U)) :=
    SheafificationUnitIso.of_iso (Opens.grothendieckTopology X.left) (formsIso k X Y g hg n) (op U)
  exact SheafificationUnitRestriction.isIso g.opensFunctor (ModuleCat.{u} k)
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology Y.left)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k Y n) (op U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamOpenSheafificationUnit
