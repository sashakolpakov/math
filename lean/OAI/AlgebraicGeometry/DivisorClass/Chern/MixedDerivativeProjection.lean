import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.OneFormProjection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault
import OAI.Analysis.DifferentialForms.Manifold.SectionCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.BidegreeIndependence

/-! # Mixed Derivative Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.MixedDerivativeProjection

noncomputable section

/-! A one-form with genuine mixed exterior derivative has Dolbeault-closed antiholomorphic part. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U V : Opens M}

theorem openManifold_two_bidegree_last_zero (A B C : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2)
    (hA : Open.ManifoldBidegree.OpenManifoldHasBidegree 2 0 A) (hB : Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 B)
    (hC : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 2 C) (hsum : A + B + C = 0) : C = 0 := by
  apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U C).mpr
  intro e he
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  have hz := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2 => a.extension.inChart e y) hsum
  have hzero : (0 : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2).extension = 0 := Analysis.DifferentialForms.Manifold.Open.openManifoldFormExtension_zero U
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
    Pi.add_apply, hzero, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero, Pi.zero_apply] at hz
  exact (AlgebraicTopology.DeRham.Comparison.BidegreeIndependence.formValue_neighbor_triple_eq_zero (p := 0) (q := 0)
    (A.extension.inChart e y) (B.extension.inChart e y) (C.extension.inChart e y)
    (hA e he y y.property) (hB e he y y.property) (hC e he y y.property) hz).2.2

theorem openManifoldOnePart_dbar_zero_of_mixed_derivative (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (ha : Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a)) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) = 0 := by
  let H := Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) a
  let A := Manifold.OneFormProjection.openManifoldOnePart Complex.I a
  let P := Open.ManifoldDolbeault.openManifoldDolbeaultPrime 1 0 1 H
  let B := Open.ManifoldDolbeault.openManifoldDolbeaultD 1 0 1 H + Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 A +
    (-1 : ℂ) • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a
  let C := Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 A
  have hH : Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 H := Manifold.OneFormProjection.openManifoldOnePart_holomorphic a
  have hA : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 1 A := Manifold.OneFormProjection.openManifoldOnePart_antiholomorphic a
  have hP : Open.ManifoldBidegree.OpenManifoldHasBidegree 2 0 P := Open.ManifoldDolbeault.openManifoldDolbeaultPrime_hasBidegree rfl hH
  have hB : Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 B := Open.ManifoldDolbeault.openManifoldHasBidegree_add
    (Open.ManifoldDolbeault.openManifoldHasBidegree_add (Open.ManifoldDolbeault.openManifoldDolbeaultD_hasBidegree rfl hH)
      (Open.ManifoldDolbeault.openManifoldDolbeaultPrime_hasBidegree rfl hA)) (Open.ManifoldDolbeault.openManifoldHasBidegree_smul (-1) ha)
  have hC : Open.ManifoldBidegree.OpenManifoldHasBidegree 0 2 C := Open.ManifoldDolbeault.openManifoldDolbeaultD_hasBidegree rfl hA
  have hd := congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart_add a)
  rw [map_add] at hd
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d H + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d A = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a at hd
  have hsum : P + B + C = 0 := by
    calc
      P + B + C =
          (Open.ManifoldDolbeault.openManifoldDolbeaultPrime 1 0 1 H + Open.ManifoldDolbeault.openManifoldDolbeaultD 1 0 1 H) +
          (Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 A + Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 A) +
          (-1 : ℂ) • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a := by
        apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
        intro x
        ext v
        change (_ + (_ + _ + (-1 : ℂ) * _)) + _ = (_ + _) + (_ + _) + (-1 : ℂ) * _
        ring
      _ = 0 := by
        rw [Open.ManifoldDolbeault.openManifoldDolbeaultPrime_add_dbar, Open.ManifoldDolbeault.openManifoldDolbeaultPrime_add_dbar, hd]
        apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
        intro x
        ext v
        change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a x v + (-1 : ℂ) * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a x v = 0
        ring
  exact openManifold_two_bidegree_last_zero P B C hP hB hC hsum

theorem openManifoldOnePart_dbar_zero_of_closed (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (ha : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) = 0 := by
  apply openManifoldOnePart_dbar_zero_of_mixed_derivative a
  rw [ha]
  intro e _ y _ z v
  have hzero : (0 : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2).extension = 0 := Analysis.DifferentialForms.Manifold.Open.openManifoldFormExtension_zero U
  rw [hzero, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero]
  simp

theorem openManifoldOneAntiProjection_restrict (h : V ≤ U) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Open.ManifoldBidegree.antiOpenManifoldFormRestrict h (Manifold.OneFormProjection.openManifoldOneAntiProjection a) =
      Manifold.OneFormProjection.openManifoldOneAntiProjection (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) :=
  Subtype.ext (Manifold.OneFormProjection.openManifoldOnePart_restrict Complex.I h a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.MixedDerivativeProjection
