import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space

/-! # Cycle Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleCoordinates.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: geometric generic-point formulas for affine-space coordinate decompositions -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

theorem affineSpaceReindexEquiv_fiberGeneric {ι κ : Type} (e : ι ≃ κ) (x : X) :
    (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X e).hom (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace κ X ↘ X) x :=
  Integral.FiberComposition.BundleCycles.integralFiberGenericPoint_iso (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X e) _ _
    (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv_over X e) x

theorem affineSpaceEmptyEquiv_fiberGeneric (ι : Type) [IsEmpty ι] (x : X) :
    (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).inv x = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x := by
  apply (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).hom.isClosedEmbedding.injective
  change (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).hom ((CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).inv x) =
    (AffineSpace ι X ↘ X) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x)
  rw [Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection]
  exact congrArg (fun k : X ⟶ X => k x) (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).inv_hom_id

theorem affineSpaceSuccEquiv_fiberGeneric (n : ℕ) (x : X) :
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).hom (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin (n + 1)) X ↘ X) x) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X))
        (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin n) X ↘ X) x) :=
  Integral.FiberComposition.BundleCycles.integralFiberGenericPoint_factorization (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n) _
    (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X)) _ (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv_over X n) x

theorem affineSpaceSuccEquiv_inverse_fiberGeneric (n : ℕ) (x : X) :
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X))
        (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin n) X ↘ X) x)) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin (n + 1)) X ↘ X) x := by
  rw [← affineSpaceSuccEquiv_fiberGeneric]
  exact congrArg (fun k => k (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin (n + 1)) X ↘ X) x))
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).hom_inv_id

end

/-! # LineBundleCycles: actual finite fiber-generic cycles in affine-space coordinates -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

theorem affineSpaceReindexEquiv_cycleExtension {ι κ : Type} (e : ι ≃ κ) (z : X →₀ ℚ) :
    Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X e).hom
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace ι X ↘ X) z) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace κ X ↘ X) z := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ z) = Finsupp.mapDomain _ z
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k z) (funext (affineSpaceReindexEquiv_fiberGeneric X e))

theorem affineSpaceEmptyEquiv_cycleExtension (ι : Type) [IsEmpty ι] (z : X →₀ ℚ) :
    Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X ι).inv z =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace ι X ↘ X) z :=
  congrArg (fun k => Finsupp.mapDomain k z) (funext (affineSpaceEmptyEquiv_fiberGeneric X ι))

theorem affineSpaceSuccEquiv_cycleExtension (n : ℕ) (z : X →₀ ℚ) :
    Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X))
          (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace (Fin n) X ↘ X) z)) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace (Fin (n + 1)) X ↘ X) z := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.mapDomain _ z)) = Finsupp.mapDomain _ z
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k z)
    (funext (affineSpaceSuccEquiv_inverse_fiberGeneric X n))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleCoordinates.BundleCycles
