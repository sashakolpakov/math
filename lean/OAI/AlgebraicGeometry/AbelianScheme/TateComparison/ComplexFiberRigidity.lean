import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberPolarizationType

/-! # Complex Fiber Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexFiberRigidity.SphericalPELAlbaneseData

noncomputable section

/-! Full-level rigidity on the actual complex fibers of the supplied
fine PEL moduli family, using its canonical iterated-pullback comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

local notation "fiberBase" => Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)

include h in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.complexFiber_abelian_eq_id (b : fiberBase ⟶ Spec (.of K)) (x : D.GeometricPoint b)
    (e : PELModuli.PELFamilyIso (D.fiberFamily b x) (D.fiberFamily b x)) :
    e.abelian.hom = 𝟙 (D.fiberFamily b x).abelian.scheme := by
  have : IsReduced (Over.mk (b ≫ D.generic)).left := inferInstanceAs (IsReduced fiberBase)
  let P := D.model.family.pullback (D.modelGeometricPoint b x).left
  have hp : P.IsPEL D.reference.polarizationType
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom :=
    (h.classifies.1 (Over.mk (b ≫ D.generic)) (D.modelGeometricPoint b x)).1
  let a : PELModuli.PELFamilyIso (D.fiberFamily b x) P :=
    D.model.family.pullbackComp (pullback.fst D.model.space.hom D.generic) x.left
  exact PELModuli.PELFamilyIso.complex_abelian_eq_id_via_ofBase (S := fiberBase) rfl e a hp h.fullLevel

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexFiberRigidity.SphericalPELAlbaneseData
