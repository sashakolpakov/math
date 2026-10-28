import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamTraceOverlap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ComplexBasisGluing

/-! # De Rham Sheaf Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTrace

noncomputable section

/-! The native finite étale trace is a morphism of the original sheaf
de Rham complexes. It is glued on a basis supplied by the geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]

abbrev sourceComplex := ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.directImage f).mapHomologicalComplex (.up ℕ)).obj
  (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

local instance (i : TraceBasis.Index R X Y f) : LinearOrder (TraceBasis.coordinateIndex R X Y f i) :=
  TraceBasis.coordinateOrder R X Y f i

def localMap (i : TraceBasis.Index R X Y f) :
    IntrinsicDeRham.SectionUnit.Intrinsic.sections R X (f.left ⁻¹ᵁ TraceBasis.opens R X Y f i) ⟶
      IntrinsicDeRham.SectionUnit.Intrinsic.sections R Y (TraceBasis.opens R X Y f i) :=
  AffineOpen.DeRhamTrace.map R X Y f (TraceBasis.opens R X Y f i) (TraceBasis.coordinateIndex R X Y f i)
    (Module.Free.chooseBasis (AffineOpen.DeRhamTrace.targetRing R Y (TraceBasis.opens R X Y f i))
      (AffineOpen.DeRhamTrace.sourceRing R X Y f (TraceBasis.opens R X Y f i)))

def basisMap : Sheaf.ComplexBasisGluing.BasisMap (TraceBasis.opens R X Y f)
    (sourceComplex R X Y f) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) where
  app := localMap R X Y f
  naturality i j h := by
    let : Fact (TraceBasis.opens R X Y f i ≤ TraceBasis.opens R X Y f j) := ⟨h⟩
    exact AffineOpen.DeRhamTraceOverlap.map_restriction R X Y f
      (TraceBasis.opens R X Y f j) (TraceBasis.opens R X Y f i)
      (TraceBasis.coordinateIndex R X Y f j) (TraceBasis.coordinateIndex R X Y f i) _ _

variable [IsProper Y.hom] [Smooth Y.hom]

def trace : sourceComplex R X Y f ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y :=
  (basisMap R X Y f).glue (TraceBasis.isBasis R X Y f)

theorem trace_app (i : TraceBasis.Index R X Y f) (n : ℕ) :
    ((trace R X Y f).f n).hom.app (op (TraceBasis.opens R X Y f i)) = (localMap R X Y f i).f n :=
  (basisMap R X Y f).glue_app (TraceBasis.isBasis R X Y f) n i

theorem trace_unique (t : sourceComplex R X Y f ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)
    (ht : ∀ i n, (t.f n).hom.app (op (TraceBasis.opens R X Y f i)) = (localMap R X Y f i).f n) :
    t = trace R X Y f :=
  (basisMap R X Y f).glue_unique (TraceBasis.isBasis R X Y f) t (fun n i => ht i n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTrace
