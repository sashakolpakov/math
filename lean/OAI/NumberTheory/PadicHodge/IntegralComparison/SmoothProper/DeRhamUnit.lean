import OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamOpenSheafificationUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamSheafificationUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCharts

/-! # De Rham Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamUnit

noncomputable section

/-! The original de Rham sheafification unit is an isomorphism on every actual affine Čech intersection. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

theorem forms (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X) (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app
      (op (CechIntersections.opens k X q t))) := by
  let C := CechIntersections.coordinateRing k X q t
  let σ := EtaleCover.coordinateIndex k X (t 0)
  let : LinearOrder σ := ChartSections.coordinateOrder k X (t 0)
  let : Algebra (MvPolynomial σ k) C := CechIntersections.polynomialAlgebra k X q t
  let : IsScalarTower k (MvPolynomial σ k) C := CechIntersections.tower k X q t
  let : Algebra.Etale (MvPolynomial σ k) C := CechIntersections.etale k X q t
  have hlocal := Affine.FrobeniusSheafificationUnit.forms_top k C σ n
  have h := @DeRhamOpenSheafificationUnit.isIso k inferInstance
    (Crystalline.Presentation.affineScheme k C) X
    (CechIntersections.chartMap k X q t)
    (CechIntersections.chartMap_open k X q t)
    (CechIntersections.chartMap_over k X q t) n ⊤ hlocal
  have hopen : CechIntersections.chartMap k X q t ''ᵁ ⊤ =
      CechIntersections.opens k X q t :=
    (CechIntersections.chartMap k X q t).image_top_eq_opensRange.trans
      (CechIntersections.chartMap_range k X q t)
  exact (congrArg (fun V : X.left.Opens => IsIso
    ((toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app (op V))) hopen).mp h

omit [Fintype k] in
theorem chart_intersection (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X) :
    (∏ᶜ fun j : Fin (q + 1) => FrobeniusCharts.opens k X (t j)) =
      CechIntersections.opens k X q t := by
  change (∏ᶜ fun j : Fin (q + 1) => FrobeniusCharts.opens k X (t j)) =
    ∏ᶜ (DeRhamZariski.opens k X ∘ t)
  congr 1
  funext j
  exact FrobeniusCharts.opens_eq k X (t j)

theorem chart_forms (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X) (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf k X n)).app
      (op (∏ᶜ fun j : Fin (q + 1) => FrobeniusCharts.opens k X (t j)))) := by
  rw [chart_intersection]
  exact forms k X q t n

theorem evaluated_isIso (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X) :
    IsIso (DeRhamSheafificationUnit.evaluatedMap k X (CechIntersections.opens k X q t)) := by
  have (n : ℕ) : IsIso ((DeRhamSheafificationUnit.evaluatedMap k X
      (CechIntersections.opens k X q t)).f n) := forms k X q t n
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamUnit
