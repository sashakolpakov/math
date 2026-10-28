import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRham

/-! # Cech De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechDeRham

noncomputable section

/-!
# IntegralComparison: native de Rham sections compute original crystalline sections on every Čech intersection
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))
  (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X)

def map :
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (CechIntersections.opens k X q t)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Global.DeRhamCoefficientComplex.complex p k X) ⟶
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (CechIntersections.opens k X q t)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I) := by
  exact @AffineOpen.DeRham.Comparison.map p inferInstance k inferInstance inferInstance inferInstance
    X (CechIntersections.opens k X q t) (CechIntersections.affine k X q t) I
    (EtaleCover.coordinateIndex k X (t 0))
    (ChartSections.coordinateOrder k X (t 0))
    (EtaleCover.coordinateIndex_fintype k X (t 0))
    (CechIntersections.polynomialAlgebra k X q t) (CechIntersections.tower k X q t) (CechIntersections.etale k X q t)

instance map_quasiIso : QuasiIso (map p k X I q t) := by
  exact @AffineOpen.DeRham.Comparison.map_quasiIso p inferInstance k inferInstance inferInstance inferInstance
    X (CechIntersections.opens k X q t) (CechIntersections.affine k X q t) I
    (EtaleCover.coordinateIndex k X (t 0))
    (ChartSections.coordinateOrder k X (t 0))
    (EtaleCover.coordinateIndex_fintype k X (t 0))
    (CechIntersections.polynomialAlgebra k X q t) (CechIntersections.tower k X q t) (CechIntersections.etale k X q t)

def homologyIso (i : ℕ) :
    (((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (CechIntersections.opens k X q t)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Global.DeRhamCoefficientComplex.complex p k X)).homology i ≅
    (((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (CechIntersections.opens k X q t)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I)).homology i :=
  isoOfQuasiIsoAt (map p k X I q t) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechDeRham
