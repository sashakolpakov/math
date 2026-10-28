import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultProjection
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeaultIdentities

/-! # One Form Projection -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction

noncomputable section

/-! Smooth degree-one type projections and the scalar correction equation for Hodge spanning. -/

open Set
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The complex-linear projection of a real covector has type (1,0). -/
theorem oneCovector_holomorphic_projection (φ : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 ((1 / 2 : ℂ) • (φ - Complex.I •
      φ.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  obtain ⟨D, rfl⟩ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).surjective φ
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E ℂ D (z : ℂ) (v 0)

/-- The conjugate-linear projection of a real covector has type (0,1). -/
theorem oneCovector_antiholomorphic_projection (φ : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 ((1 / 2 : ℂ) • (φ + Complex.I •
      φ.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  obtain ⟨D, rfl⟩ := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).surjective φ
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, one_mul, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E ℂ D (z : ℂ) (v 0)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The smooth holomorphic projection uses the actual complex tangent action. -/
def oneFormHolomorphicPart : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 :=
  (1 / 2 : ℂ) • (LinearMap.id - Complex.I •
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)

/-- The smooth antiholomorphic projection is the complementary tangent projection. -/
def oneFormAntiholomorphicPart : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 :=
  (1 / 2 : ℂ) • (LinearMap.id + Complex.I •
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)

theorem oneFormHolomorphicPart_hasBidegree (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (oneFormHolomorphicPart form).val := by
  intro e he y hy
  have hsub (α β : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 1) :
      (α - β).inChart e = α.inChart e - β.inChart e := by
    funext z
    ext v
    rfl
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 (((1 / 2 : ℂ) • (form.val - Complex.I •
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ form.val)).inChart e y)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, hsub,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.sub_apply,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart _ _ e he hy, inv_inv,
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]
  exact oneCovector_holomorphic_projection _

theorem oneFormAntiholomorphicPart_hasBidegree (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 (oneFormAntiholomorphicPart form).val := by
  intro e he y hy
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (((1 / 2 : ℂ) • (form.val + Complex.I •
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ form.val)).inChart e y)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.add_apply,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart _ _ e he hy, inv_inv,
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]
  exact oneCovector_antiholomorphic_projection _

/-- These actual smooth forms add to the given one-form. -/
theorem oneForm_parts_add (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) :
    oneFormHolomorphicPart form + oneFormAntiholomorphicPart form = form := by
  change (1 / 2 : ℂ) • (form - Complex.I • _) +
    (1 / 2 : ℂ) • (form + Complex.I • _) = form
  module

/-- Every zero-form has the unique nullary bidegree (0,0). -/
def zeroFormPure (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 0 :=
  ⟨form, by
    intro e _ y _ z v
    simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, mul_one, one_mul]
    congr 1
    funext i
    exact Fin.elim0 i⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The type projection of a scalar differential agrees with the existing
geometric Dolbeault differential. -/
theorem oneFormHolomorphicPart_d_eq_dPrime (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    oneFormHolomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) =
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (zeroFormPure form)).val := by
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_coe, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self,
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultPrimeForm_apply]
  change (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form - Complex.I • _) =
    (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form +
      (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 0)⁻¹ • _)
  simp [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter,
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe, Complex.inv_I, sub_eq_add_neg, neg_smul, zeroFormPure]

/-- The scalar correction operator is exactly minus the actual `d' d''`.
Thus its solvability is the degree-(1,1) analytic correction needed for spanning. -/
theorem scalar_correction_eq_neg_dPrimeDoublePrime (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form)) =
      -(Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime (zeroFormPure form)).val := by
  rw [oneFormHolomorphicPart_d_eq_dPrime]
  have hd := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (zeroFormPure form))
  simp only [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_squared, ZeroMemClass.coe_zero,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self, zero_add] at hd
  rw [← hd]
  have hm := congrArg Subtype.val
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_dPrime_add_dPrime_dDoublePrime (zeroFormPure form))
  exact eq_neg_of_add_eq_zero_left hm

/-- Once the holomorphic part of a closed one-form is closed, its other part
is closed as well. -/
theorem oneForm_antiholomorphicPart_closed
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (hh : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart form.val) = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormAntiholomorphicPart form.val) = 0 := by
  have h := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneForm_parts_add form.val)
  rwa [map_add, hh, zero_add, form.property] at h

/-- The failure of the holomorphic part of a closed one-form to be closed is
an actual exact form of pure type (1,1). -/
theorem oneFormHolomorphicPart_derivative_hasBidegree
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart form.val)).val := by
  let h : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 1 0 :=
    ⟨oneFormHolomorphicPart form.val, oneFormHolomorphicPart_hasBidegree form.val⟩
  let a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1 :=
    ⟨oneFormAntiholomorphicPart form.val, oneFormAntiholomorphicPart_hasBidegree form.val⟩
  let A : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 := (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime h).val
  let B : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime h).val + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime a).val
  let C : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 := (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a).val
  have hh : A + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime h).val = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h.val := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self] using Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime h
  have ha : (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime a).val + C = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self] using Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime a
  have hsum : A + B + C = 0 := by
    have hz := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneForm_parts_add form.val)
    rw [map_add, form.property] at hz
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h.val + Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = 0 at hz
    rw [← hh, ← ha] at hz
    dsimp only [B]
    calc
      _ = (A + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime h).val) +
        ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime a).val + C) := by abel
      _ = 0 := hz
  have hraw : A.val + B.val + C.val = 0 := congrArg Subtype.val hsum
  have hAzero := (AlgebraicTopology.DeRham.Comparison.BidegreeIndependence.rawManifoldForm_neighbor_triple_eq_zero (p := 0) (q := 0)
    A.val B.val C.val
    (fun z => (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime h).hasManifoldBidegree.complexAction_eq z)
    (fun z => ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime h).hasManifoldBidegree.add
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime a).hasManifoldBidegree).complexAction_eq z)
    (fun z => (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a).hasManifoldBidegree.complexAction_eq z) hraw).1
  have hAzero' : A = 0 := Subtype.ext hAzero
  rw [hAzero', zero_add] at hh
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h.val).val
  rw [← hh]
  exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime h).hasManifoldBidegree

/-- On a compact complex manifold the homogeneous scalar correction equation
has only locally constant solutions, stated through their zero differential. -/
theorem scalar_correction_kernel [FiniteDimensional ℝ E] [CompactSpace M]
    (primitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hzero : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive)) = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = 0 := by
  let form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1 :=
    ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared primitive⟩
  let α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1 := ⟨oneFormHolomorphicPart form.val, hzero⟩
  let β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1 :=
    ⟨oneFormAntiholomorphicPart form.val, oneForm_antiholomorphicPart_closed form hzero⟩
  apply Intersection.CM.Construction.d_eq_zero_of_holomorphic_sub_antiholomorphic primitive α (-β)
    (oneFormHolomorphicPart_hasBidegree form.val)
    ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M 0 1).neg_mem
      (oneFormAntiholomorphicPart_hasBidegree form.val))
  change form.val = α.val - -β.val
  rw [sub_neg_eq_add]
  exact (oneForm_parts_add form.val).symm

/-- Solving the scalar correction equation supplies closed representatives of
both types in the original de Rham class. -/
theorem hodge_split_of_scalar_correction (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (primitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hsolve : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive)) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart form.val)) :
    ∃ (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1),
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 α.val.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 β.val.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 form =
        Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 α + Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 β := by
  let corrected : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1 :=
    ⟨form.val - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive, by
      change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (form.val - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive) = 0
      rw [map_sub, form.property, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared, sub_self]⟩
  have hh : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (oneFormHolomorphicPart corrected.val) = 0 := by
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
      (oneFormHolomorphicPart (form.val - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive)) = 0
    rw [map_sub, map_sub, hsolve, sub_self]
  let α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1 := ⟨oneFormHolomorphicPart corrected.val, hh⟩
  let β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1 :=
    ⟨oneFormAntiholomorphicPart corrected.val, oneForm_antiholomorphicPart_closed corrected hh⟩
  refine ⟨α, β, oneFormHolomorphicPart_hasBidegree corrected.val,
    oneFormAntiholomorphicPart_hasBidegree corrected.val, ?_⟩
  have hc : α + β = corrected := Subtype.ext (oneForm_parts_add corrected.val)
  rw [← map_add, hc]
  apply (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_eq_iff E M 1 form corrected).mpr
  refine ⟨primitive, ?_⟩
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = form.val -
    (form.val - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive)
  abel

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction
