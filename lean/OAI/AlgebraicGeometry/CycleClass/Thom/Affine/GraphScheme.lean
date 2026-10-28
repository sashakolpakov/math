import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphRingMap
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Graph Scheme -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphScheme.Constructions

noncomputable section

/-! The surjective tensor coordinate map defines a genuine closed immersion over the complex base, with its specified projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphRingMap.Constructions

variable {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ A]

theorem affineSpec_comp (h : R →ₐ[ℂ] S) (f : S →ₐ[ℂ] A) :
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S A f ≫ Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R S h =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (f.comp h) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom h.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

def graphSchemeMap (h : R →ₐ[ℂ] A) (f : S →ₐ[ℂ] A) :
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⊗[ℂ] S) :=
  Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (R ⊗[ℂ] S) A (GraphRingMap.Constructions.graphRingMap h f)

theorem graphSchemeMap_closedImmersion (h : R →ₐ[ℂ] A) (f : S →ₐ[ℂ] A)
    (hf : Function.Surjective f) : IsClosedImmersion (graphSchemeMap h f).left :=
  IsClosedImmersion.spec_of_surjective _ (GraphRingMap.Constructions.graphRingMap_surjective h f hf)

theorem graphSchemeMap_left (h : R →ₐ[ℂ] A) (f : S →ₐ[ℂ] A) :
    graphSchemeMap h f ≫
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⊗[ℂ] S) Algebra.TensorProduct.includeLeft =
        Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A h := by
  rw [graphSchemeMap, affineSpec_comp, GraphRingMap.Constructions.graphRingMap_left]

theorem graphSchemeMap_right (h : R →ₐ[ℂ] A) (f : S →ₐ[ℂ] A) :
    graphSchemeMap h f ≫
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S (R ⊗[ℂ] S) Algebra.TensorProduct.includeRight =
        Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S A f := by
  rw [graphSchemeMap, affineSpec_comp, GraphRingMap.Constructions.graphRingMap_right]

theorem graphSchemeMap_point (h : R →ₐ[ℂ] A) (f : S →ₐ[ℂ] A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (graphSchemeMap h f) (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (R ⊗[ℂ] S) (x.comp (GraphRingMap.Constructions.graphRingMap h f)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap (GraphRingMap.Constructions.graphRingMap h f) x).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphScheme.Constructions
