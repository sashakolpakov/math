import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe
import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.Division
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Germ Slice Division -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermSliceDivision.AnalyticLocal

noncomputable section

/-! Exact division identifies the kernel of restriction to a coordinate
slice in the actual local ring of holomorphic germs. -/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem germ_coordinate_division (x : E) (c : ℂ) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) :
    ∃ b : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c),
      a = GermPolynomialNe.AnalyticLocal.parameterInclusion x c (GermPolynomialNe.AnalyticLocal.sliceEvaluation x c a) + GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c * b := by
  obtain ⟨F, hFa, W, hW, hxc, hF⟩ := a.property
  obtain ⟨R, U, hR, hU, hx, hUW⟩ := Coordinate.Division.Weierstrass.exists_product_closedDisk hW hxc
  obtain ⟨Q, hQ, hformula⟩ := Coordinate.Division.Weierstrass.coordinate_division hW hF hU hR hUW
  have hxcU : (x, c) ∈ U ×ˢ ball c R := ⟨hx, mem_ball_self hR⟩
  let b := ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction (x, c) Q (hU.prod isOpen_ball) hxcU hQ
  have hs : (GermPolynomialNe.AnalyticLocal.parameterInclusion x c (GermPolynomialNe.AnalyticLocal.sliceEvaluation x c a)).val =
      ((fun p : E × ℂ => F (p.1, c)) : Germ (𝓝 (x, c)) ℂ) := by
    change GermComposition.AnalyticLocal.germComposition Prod.fst _ (GermComposition.AnalyticLocal.germComposition (fun y : E => (y, c)) _ a.val) = _
    rw [← hFa]
    rfl
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change a.val = (GermPolynomialNe.AnalyticLocal.parameterInclusion x c (GermPolynomialNe.AnalyticLocal.sliceEvaluation x c a)).val +
    (GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c).val * (Q : Germ (𝓝 (x, c)) ℂ)
  rw [← hFa, hs, GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm_val]
  apply Germ.coe_eq.mpr
  filter_upwards [(hU.prod isOpen_ball).mem_nhds hxcU] with p hp
  exact hformula p.1 hp.1 p.2 hp.2

theorem sliceEvaluation_eq_zero_iff (x : E) (c : ℂ) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) :
    GermPolynomialNe.AnalyticLocal.sliceEvaluation x c a = 0 ↔ GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c ∣ a := by
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := germ_coordinate_division x c a
    rw [ha, map_zero, zero_add] at hb
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    rw [map_mul, GermPolynomialNe.AnalyticLocal.sliceEvaluation_centeredCoordinate, zero_mul]

theorem sliceEvaluation_ker (x : E) (c : ℂ) :
    RingHom.ker (GermPolynomialNe.AnalyticLocal.sliceEvaluation x c) = Ideal.span {GermPolynomialNe.AnalyticLocal.centeredCoordinateGerm x c} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, sliceEvaluation_eq_zero_iff]

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermSliceDivision.AnalyticLocal
