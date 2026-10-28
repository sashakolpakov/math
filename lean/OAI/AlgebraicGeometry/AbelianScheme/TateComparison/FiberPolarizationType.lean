import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationTypeTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFlags

/-! # Fiber Polarization Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The reference polarization type on every actual geometric fiber
follows from the supplied IntegralModel moduli classification and canonical
comparison of the two base-change paths. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)
  {k : Type} [Field k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.modelGeometricPoint : Over.mk (b ≫ D.generic) ⟶ D.model.space :=
  Over.homMk (x.left ≫ pullback.fst D.model.space.hom D.generic) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ D.generic) x.w)

include h in
theorem Data.SphericalPELAlbaneseData.fiberPolarizationType :
    (D.fiberFamily b x).polarizationMap.HasPolarizationType D.reference.polarizationType := by
  have : IsReduced (Over.mk (b ≫ D.generic)).left := inferInstanceAs (IsReduced (Spec (.of k)))
  have hp := (h.classifies.1 (Over.mk (b ≫ D.generic)) (D.modelGeometricPoint b x)).1.1
  exact (D.model.family.pullbackComp (pullback.fst D.model.space.hom D.generic) x.left).polarizationType
    D.reference.polarizationType hp

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
