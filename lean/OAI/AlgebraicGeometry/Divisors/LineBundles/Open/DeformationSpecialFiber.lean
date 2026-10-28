import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationTo

/-! # Deformation Special Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationSpecialFiber.BundleCycles

noncomputable section

section

/-! The zero fiber of the open deformation is the actual cartesian restriction of the original zero fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

def globalOpenSpecialFiberMap : Global.SpecialFiber.BundleCycles.globalSpecialFiber (I.comap i) ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber I :=
  (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback I).lift
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i) ≫ Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I)
    (QuotientFiber.BundleCycles.globalSpecialFiberToZero (I.comap i))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i) ≫ k)
        (DeformationTo.BundleCycles.globalOpenDeformationMap_parameter i I)).trans (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback (I.comap i)).w))

theorem globalOpenSpecialFiberMap_toDeformation :
    globalOpenSpecialFiberMap i I ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I =
      Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i) ≫ Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I :=
  (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback I).lift_fst _ _ _

theorem globalOpenSpecialFiberMap_toZero :
    globalOpenSpecialFiberMap i I ≫ QuotientFiber.BundleCycles.globalSpecialFiberToZero I =
      QuotientFiber.BundleCycles.globalSpecialFiberToZero (I.comap i) :=
  (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback I).lift_snd _ _ _

theorem globalOpenSpecialFiberMap_isPullback :
    IsPullback (globalOpenSpecialFiberMap i I) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i))
      (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) := by
  have h : IsPullback (globalOpenSpecialFiberMap i I ≫ QuotientFiber.BundleCycles.globalSpecialFiberToZero I)
      (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i)) QuotientFiber.BundleCycles.parameterZeroInclusion
      (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I ≫ Deformation.Parameter.BundleCycles.globalDeformationParameter I) := by
    rw [globalOpenSpecialFiberMap_toZero, DeformationTo.BundleCycles.globalOpenDeformationMap_parameter]
    exact (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback (I.comap i)).flip
  exact h.of_right (globalOpenSpecialFiberMap_toDeformation i I) (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback I).flip

instance globalOpenSpecialFiberMap_open : IsOpenImmersion (globalOpenSpecialFiberMap i I) :=
  MorphismProperty.of_isPullback (globalOpenSpecialFiberMap_isPullback i I).flip inferInstance

theorem globalOpenSpecialFiberMap_range :
    Set.range (globalOpenSpecialFiberMap i I) =
      Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I ⁻¹' Set.range (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) := by
  have h := Scheme.image_preimage_eq_of_isPullback (globalOpenSpecialFiberMap_isPullback i I).flip Set.univ
  simpa only [Set.preimage_univ, Set.image_univ] using h

end

/-! The open zero-fiber map lies over the original open immersion of base schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

theorem globalOpenSpecialFiberMap_toBase :
    globalOpenSpecialFiberMap i I ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I =
      Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (I.comap i) ≫ i := by
  rw [← Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase, ← Category.assoc, globalOpenSpecialFiberMap_toDeformation,
    Category.assoc, DeformationTo.BundleCycles.globalOpenDeformationMap_toBase, ← Category.assoc, Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase]

theorem globalOpenSpecialFiberMap_base_isPullback :
    IsPullback (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (I.comap i)) (globalOpenSpecialFiberMap i I)
      i (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I) := by
  have h := ((globalOpenSpecialFiberMap_isPullback i I).paste_vert
    (DeformationTo.BundleCycles.globalOpenDeformationMap_isPullback i I).flip).flip
  rw [Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase, Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationSpecialFiber.BundleCycles
