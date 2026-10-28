import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechDeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamNaturality

/-! # Cech De Rham Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechDeRhamNaturality

noncomputable section

/-! The original de Rham-crystalline comparison is natural on homology over actual Cech intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))
  (m n : ℕ) (s : Fin (m + 1) → EtaleCover.Index k X)
  (t : Fin (n + 1) → EtaleCover.Index k X)
  (h : CechIntersections.opens k X n t ≤ CechIntersections.opens k X m s)

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (CechDeRham.map p k X I m s ≫
        Bounded.ChartEvaluationRestriction.map (Witt.Crystalline.wittStructureMap p k X) 0 I h) i =
    HomologicalComplex.homologyMap
      (AffineOpen.DeRhamRestriction.map p k X h ≫ CechDeRham.map p k X I n t) i :=
  @AffineOpen.DeRhamNaturality.homology p inferInstance k inferInstance inferInstance inferInstance
    X (CechIntersections.opens k X m s) (CechIntersections.opens k X n t) h (CechIntersections.affine k X m s) (CechIntersections.affine k X n t) I
    (EtaleCover.coordinateIndex k X (s 0))
    (EtaleCover.coordinateIndex k X (t 0))
    (ChartSections.coordinateOrder k X (s 0))
    (ChartSections.coordinateOrder k X (t 0))
    (EtaleCover.coordinateIndex_fintype k X (s 0))
    (EtaleCover.coordinateIndex_fintype k X (t 0))
    (CechIntersections.polynomialAlgebra k X m s) (CechIntersections.tower k X m s) (CechIntersections.etale k X m s)
    (CechIntersections.polynomialAlgebra k X n t) (CechIntersections.tower k X n t) (CechIntersections.etale k X n t) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechDeRhamNaturality
