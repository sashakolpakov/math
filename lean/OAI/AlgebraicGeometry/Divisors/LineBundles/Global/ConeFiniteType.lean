import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationFiniteType

/-! # Cone Finite Type -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ConeFiniteType.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite type and Noetherianity of the actual global cone

The proved closed-fiber immersion and the constructed deformation
projection give these properties without any regularity of the center.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

instance globalSpecialFiber_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (SpecialFiber.BundleCycles.globalSpecialFiber I) :=
  LocallyOfFiniteType.isLocallyNoetherian (SpecialFiber.BundleCycles.globalSpecialFiberMap I)

instance globalSpecialFiber_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (SpecialFiber.BundleCycles.globalSpecialFiber I) := by
  have : CompactSpace (SpecialFiber.BundleCycles.globalSpecialFiber I) :=
    QuasiCompact.compactSpace_of_compactSpace (SpecialFiber.BundleCycles.globalSpecialFiberMap I)
  exact ⟨⟩

instance globalSpecialFiberProjection_locallyOfFiniteType [IsLocallyNoetherian X] :
    LocallyOfFiniteType (SpecialFiber.BundleCycles.globalSpecialFiberProjection I) := by
  have hg : LocallyOfFiniteType (Deformation.BundleCycles.globalDeformationProjection I) :=
    DeformationFiniteType.BundleCycles.globalDeformationProjection_locallyOfFiniteType I
  have h : LocallyOfFiniteType (SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ Deformation.BundleCycles.globalDeformationProjection I) := inferInstance
  exact (congrArg (fun g => LocallyOfFiniteType g) (SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase I)).mp h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ConeFiniteType.BundleCycles
