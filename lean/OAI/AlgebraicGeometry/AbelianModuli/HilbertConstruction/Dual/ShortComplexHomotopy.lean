import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexEndpointHomotopy

/-! # Short Complex Homotopy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ShortComplexHomotopy

noncomputable section

/-! Reversing a short-complex homotopy equivalence and applying the actual module dual preserves its homology comparison, without any exactness hypothesis on duality. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v

def shortComplexHomotopyEquivOp
    {V : Type u} [Category.{v} V] [Preadditive V]
    {S T : ShortComplex V} (e : ShortComplex.HomotopyEquiv S T) :
    ShortComplex.HomotopyEquiv S.op T.op where
  hom := ShortComplex.opMap e.inv
  inv := ShortComplex.opMap e.hom
  homotopyHomInvId := e.homotopyHomInvId.op
  homotopyInvHomId := e.homotopyInvHomId.op

def dualShortComplexHomotopyEquiv
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)}
    (e : ShortComplex.HomotopyEquiv S T) :
    ShortComplex.HomotopyEquiv (Module.DualFunctor.dualModuleShortComplex S) (Module.DualFunctor.dualModuleShortComplex T) :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMap (Module.DualFunctor.moduleDualFunctor R)
    (shortComplexHomotopyEquivOp e)

theorem dualShortComplex_exact_iff_of_homotopyEquiv
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)}
    (e : ShortComplex.HomotopyEquiv S T) :
    (Module.DualFunctor.dualModuleShortComplex S).Exact ↔ (Module.DualFunctor.dualModuleShortComplex T).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, ShortComplex.exact_iff_isZero_homology]
  exact (ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivHomologyIso
    (dualShortComplexHomotopyEquiv e)).isZero_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ShortComplexHomotopy
