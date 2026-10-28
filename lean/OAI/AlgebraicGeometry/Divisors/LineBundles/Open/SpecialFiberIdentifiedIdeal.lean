import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationSpecialFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GlobalCycleSpecialization

/-! # Special Fiber Identified Ideal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SpecialFiberIdentifiedIdeal.BundleCycles

noncomputable section

/-! The open zero-fiber construction respects an equality with the actual source center ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)
    (J : X.IdealSheafData) (h : I.comap i = J)

def globalOpenSpecialFiberWithIdeal : Global.SpecialFiber.BundleCycles.globalSpecialFiber J ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber I :=
  eqToHom (congrArg Global.SpecialFiber.BundleCycles.globalSpecialFiber h.symm) ≫ DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap i I

instance globalOpenSpecialFiberWithIdeal_open : IsOpenImmersion (globalOpenSpecialFiberWithIdeal i I J h) := by
  subst J
  simpa only [globalOpenSpecialFiberWithIdeal, eqToHom_refl, Category.id_comp] using
    DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap_open i I

theorem globalOpenSpecialFiberWithIdeal_toBase :
    globalOpenSpecialFiberWithIdeal i I J h ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I =
      Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection J ≫ i := by
  subst J
  simpa only [globalOpenSpecialFiberWithIdeal, eqToHom_refl, Category.id_comp] using
    DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap_toBase i I

theorem globalOpenSpecialFiberWithIdeal_isPullback :
    IsPullback (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection J) (globalOpenSpecialFiberWithIdeal i I J h)
      i (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I) := by
  subst J
  simpa only [globalOpenSpecialFiberWithIdeal, eqToHom_refl, Category.id_comp] using
    DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap_base_isPullback i I

theorem globalCycleSpecialization_open_identified [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (z : Y →₀ ℚ) :
    Finsupp.comapDomain (globalOpenSpecialFiberWithIdeal i I J h) (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization I z)
      (globalOpenSpecialFiberWithIdeal i I J h).isOpenEmbedding.injective.injOn =
      Global.CycleSpecialization.BundleCycles.globalCycleSpecialization J (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  subst J
  simpa only [globalOpenSpecialFiberWithIdeal, eqToHom_refl, Category.id_comp] using
    GlobalCycleSpecialization.BundleCycles.globalCycleSpecialization_open i I z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SpecialFiberIdentifiedIdeal.BundleCycles
