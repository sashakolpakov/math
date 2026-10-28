import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor

/-! # Free Double Dual Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDoubleDualComplex

noncomputable section

/-! Finite free complexes identify with their actual double dual through evaluation, compatibly with all differentials. The symmetric opposite keeps the original indexing shape exactly. -/
open _root_.CategoryTheory
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}

def dualModuleComplexSymm (K : HomologicalComplex (ModuleCat.{u} R) c.symm) :
    HomologicalComplex (ModuleCat.{u} R) c :=
  ((HilbertConstruction.Module.DualFunctor.moduleDualFunctor R).mapHomologicalComplex c).obj K.opSymm

def finiteFreeDoubleDualComplexIso (C : HomologicalComplex (ModuleCat.{u} R) c)
    (hfin : ∀ i, Module.Finite R (C.X i)) (hfree : ∀ i, Module.Free R (C.X i)) :
    C ≅ dualModuleComplexSymm (HilbertConstruction.Module.DualFunctor.dualModuleComplex C) := by
  letI (i : ι) : Module.Finite R (C.X i) := hfin i
  letI (i : ι) : Module.Free R (C.X i) := hfree i
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (Module.evalEquiv R (C.X i)).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  ext x
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDoubleDualComplex
