import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Cycle Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleGrading.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual dimension shift of every affine-space fiber generic point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineSpaceFinFiberGenericPoint_dimension (n : ℕ) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin n) X ↘ X) x))
        ((AffineSpace (Fin n) X ↘ X) ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + n := by
  induction n with
  | zero =>
    have h := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)).hom f
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin 0) X ↘ X) x)
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm
      ((AffineSpace (Fin 0) X ↘ X) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin 0) X ↘ X) x))) f = _ at h
    rw [Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection] at h
    exact h.symm
  | succ n ih =>
    have h := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).hom
      (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X) ≫ ((AffineSpace (Fin n) X ↘ X) ≫ f))
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin (n + 1)) X ↘ X) x)
    have he : (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).hom ≫
        (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X) ≫ ((AffineSpace (Fin n) X ↘ X) ≫ f)) =
          (AffineSpace (Fin (n + 1)) X ↘ X) ≫ f :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ f) (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv_over X n))
    rw [he, CycleCoordinates.BundleCycles.affineSpaceSuccEquiv_fiberGeneric, AffineLine.CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension, ih] at h
    exact h.symm.trans (Nat.add_assoc _ _ _)

theorem affineSpaceFiberGenericPoint_dimension (ι : Type) [Finite ι] (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x))
        ((AffineSpace ι X ↘ X) ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + Nat.card ι := by
  let e := CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X (Finite.equivFin ι)
  have he : e.hom ≫ ((AffineSpace (Fin (Nat.card ι)) X ↘ X) ≫ f) =
      (AffineSpace ι X ↘ X) ≫ f := by
    rw [← Category.assoc, CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv_over]
  have h := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion e.hom
    ((AffineSpace (Fin (Nat.card ι)) X ↘ X) ≫ f)
    (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x)
  rw [he] at h
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm
    ((CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X (Finite.equivFin ι)).hom
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x))) _ = _ at h
  rw [CycleCoordinates.BundleCycles.affineSpaceReindexEquiv_fiberGeneric, affineSpaceFinFiberGenericPoint_dimension] at h
  exact h.symm

end

/-! # LineBundleCycles: the actual finite-affine-space pullback of dimension-graded cycles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (ι : Type) [Finite ι]

def affineSpaceDimensionPointMap (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι) :=
  fun x => ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X) x.1,
    (affineSpaceFiberGenericPoint_dimension X f ι x.1).trans
      (congrArg (fun n => n + Nat.card ι) x.2)⟩

def affineSpaceGradedCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (affineSpaceDimensionPointMap X f ι d)

theorem affineSpaceGradedCycleExtension_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)
        (affineSpaceGradedCycleExtension X f ι d z) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace ι X ↘ X) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι))
      (Finsupp.mapDomain (affineSpaceDimensionPointMap X f ι d) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X))
      (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleGrading.BundleCycles
