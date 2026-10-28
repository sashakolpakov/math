import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDoubleDualComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualBaseChange

/-! # Complex Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ComplexBaseChange

noncomputable section

/-! Finite free complex duality commutes with scalar extension for the symmetric indexing convention. -/
open _root_.CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}

def dualModuleComplexSymmBaseChangeIso (B : Type u) [CommRing B] [Algebra R B]
    (K : HomologicalComplex (ModuleCat.{u} R) c.symm)
    (hfin : ∀ i, Module.Finite R (K.X i)) (hfree : ∀ i, Module.Free R (K.X i)) :
    ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex c).obj
        (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm K) ≅
      HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm
        (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex c.symm).obj K) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => by
      letI : Module.Finite R (K.X i) := hfin i
      letI : Module.Free R (K.X i) := hfree i
      exact (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv B (K.X i)).toModuleIso) ?_
  intro i j _
  have : Module.Finite R (K.X i) := hfin i
  have : Module.Finite R (K.X j) := hfin j
  have : Module.Free R (K.X i) := hfree i
  have : Module.Free R (K.X j) := hfree j
  exact ModuleCat.hom_ext (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv_naturality B (K.d j i).hom).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ComplexBaseChange
