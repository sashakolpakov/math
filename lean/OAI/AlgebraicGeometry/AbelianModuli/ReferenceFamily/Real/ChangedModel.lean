import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodHodgeTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ThetaConstructionPolarization
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PositivePeriods

/-! # Changed Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.ChangedModel

noncomputable section

/-! Algebraize any real symplectic change of the original native period
marking. The result retains the exact integral Chern matrix, original
ordered marking, transported lattice and positive Riemann form. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped BigOperators TensorProduct

variable {g : ℕ} (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index g) A)
    (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)

def nativeRealChangedPeriodMap : Picard.ThetaConstruction.DefinitionsIntegral.CVec g →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (PeriodHodgeTransport.realChangedComplexPeriodMap A u).comp
    ((Integral.MarkingRationalBasis.integralMarkingRationalBasis A b).baseChange ℂ).equivFun.symm.toLinearMap

theorem nativeRealChangedPeriodMap_apply (z : Picard.ThetaConstruction.DefinitionsIntegral.CVec g) :
    nativeRealChangedPeriodMap A b u z = ∑ i, z i • u.symm (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) := by
  change PeriodHodgeTransport.realChangedComplexPeriodMap A u
    (((Integral.MarkingRationalBasis.integralMarkingRationalBasis A b).baseChange ℂ).equivFun.symm z) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, Module.Basis.baseChange_apply]
  apply Finset.sum_congr rfl
  intro i _
  change z i • ((1 : ℂ) • u.symm (Integral.MarkingRationalBasis.integralMarkingRationalBasis A b i).val) = _
  rw [one_smul, Integral.MarkingRationalBasis.integralMarkingRationalBasis_coe]

theorem nativeRealChangedPeriodMap_real (x : Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℝ) :
    nativeRealChangedPeriodMap A b u (fun i => (x i : ℂ)) =
      u.symm (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ))) := by
  rw [nativeRealChangedPeriodMap_apply, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (x i : ℂ) • u.symm (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) = x i • u.symm (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :=
      IsScalarTower.algebraMap_smul ℂ (x i) _
    _ = u.symm (x i • (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) := (u.symm.map_smul _ _).symm
    _ = u.symm ((x i : ℂ) • (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) :=
      congrArg u.symm (IsScalarTower.algebraMap_smul ℂ (x i) _).symm

theorem nativeRealChangedPeriodMap_integer (n : Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℤ) :
    nativeRealChangedPeriodMap A b u (fun i => (n i : ℂ)) =
      u.symm (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (n i : ℂ))) := by
  simpa only [Complex.ofReal_intCast] using nativeRealChangedPeriodMap_real A b u (fun i => (n i : ℝ))

theorem nativeRealChangedPeriodMap_real_bijective :
    Function.Bijective (fun x : Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℝ =>
      nativeRealChangedPeriodMap A b u (fun i => (x i : ℂ))) := by
  have h : (fun x : Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℝ => nativeRealChangedPeriodMap A b u (fun i => (x i : ℂ))) =
      u.symm ∘ (fun x : Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℝ => ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ))) :=
    funext (nativeRealChangedPeriodMap_real A b u)
  rw [h]
  exact u.symm.bijective.comp (Picard.ThetaConstruction.IntrinsicPolarization.Geometric.native_real_period_bijective A b)

theorem nativeRealChangedPeriodMap_kernel :
    (nativeRealChangedPeriodMap A b u).ker =
      ((Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker.map (PeriodHodgeTransport.realPeriodComplexification A u).toLinearMap).comap
        ((Integral.MarkingRationalBasis.integralMarkingRationalBasis A b).baseChange ℂ).equivFun.symm.toLinearMap := by
  rw [nativeRealChangedPeriodMap, LinearMap.ker_comp, PeriodHodgeTransport.realChangedComplexPeriodMap_kernel]

variable (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    (hu : ∀ x y, (Intrinsic.RiemannForm.nativeRiemannForm A L hL (u x) (u y)).im =
      (Intrinsic.RiemannForm.nativeRiemannForm A L hL x y).im)

include hu in
theorem exists_nativeRealChangedPolarizedTorus :
    ∃ (T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b))
      (e : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] Picard.ThetaConstruction.DefinitionsIntegral.Tangent g),
      (∀ z, T.periodMap z = e (nativeRealChangedPeriodMap A b u z)) ∧
      (∀ v, v ∈ T.lattice ↔ u (e.symm v) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ∧
      (∀ x y, T.riemannForm (e x) (e y) = Intrinsic.RiemannForm.nativeRiemannForm A L hL x y) := by
  let e := Picard.ThetaConstruction.IntrinsicPolarization.Geometric.nativeTangentCoordinates A b
  let π := e.toLinearMap.comp (nativeRealChangedPeriodMap A b u)
  have hreal : Function.Bijective ((π.restrictScalars ℝ).comp Picard.ThetaConstruction.DefinitionsIntegral.realInclusion) :=
    e.bijective.comp (nativeRealChangedPeriodMap_real_bijective A b u)
  obtain ⟨Γ, hΓ, hd, hc⟩ := Picard.ThetaConstruction.DefinitionsIntegral.marked_lattice π hreal
  let H₀ := Intrinsic.RiemannForm.nativeRiemannForm A L hL
  let H : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g →ₗ⋆[ℂ] Picard.ThetaConstruction.DefinitionsIntegral.Tangent g →ₗ[ℂ] ℂ :=
    (H₀.comp e.symm.toLinearMap).compl₂ e.symm.toLinearMap
  have hH (x y : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) : H x y = H₀ (e.symm x) (e.symm y) := rfl
  have hsym (x y : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) : H y x = star (H x y) :=
    Intrinsic.RiemannForm.nativeRiemannForm_symmetry A L hL (e.symm x) (e.symm y)
  have hpos (x : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) (hx : x ≠ 0) : 0 < (H x x).re :=
    Intrinsic.RiemannForm.nativeRiemannForm_positive A L hL (e.symm x)
      (fun hz => hx (e.symm.injective (hz.trans e.symm.map_zero.symm)))
  have hmark (x y : Picard.ThetaConstruction.DefinitionsIntegral.Index g → ℝ) :
      (H (π (fun i => (x i : ℂ))) (π (fun i => (y i : ℂ)))).im =
        (Picard.ThetaConstruction.DefinitionsIntegral.pairing (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b)
          (fun i => (x i : ℂ)) (fun i => (y i : ℂ))).re := by
    simp only [hH, π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply,
      nativeRealChangedPeriodMap_real]
    have h := hu (u.symm (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ))))
      (u.symm (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (y i : ℂ))))
    rw [u.apply_symm_apply, u.apply_symm_apply] at h
    exact h.symm.trans (Picard.ThetaConstruction.IntrinsicPolarization.Geometric.native_polarization_marking A L hL b
      (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b) (Intrinsic.ThetaConstructionPolarization.nativeIntegralChernMatrix_preserves A L hL b) x y)
  have hint : ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ n : ℤ, (H x y).im = (n : ℝ) := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := (hΓ x).mp hx
    obtain ⟨m, rfl⟩ := (hΓ y).mp hy
    refine ⟨∑ i, ∑ j, n i * Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b i j * m j, ?_⟩
    simpa [Picard.ThetaConstruction.DefinitionsIntegral.pairing] using hmark (fun i => (n i : ℝ)) (fun i => (m i : ℝ))
  let : DiscreteTopology Γ := hd
  let : CompactSpace (Picard.ThetaConstruction.DefinitionsIntegral.Tangent g ⧸ Γ) := hc
  let T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b) := {
    periodMap := π
    real_marking := hreal
    lattice := Γ
    lattice_marking := hΓ
    discrete := hd
    compact := hc
    projective := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (Picard.ThetaConstruction.DefinitionsIntegral.Tangent g) Γ).mpr ⟨H, hsym, hpos, hint⟩
    riemannForm := H
    hermitian := hsym
    positive := hpos
    polarization_marking := hmark }
  refine ⟨T, e, fun _ => rfl, ?_, ?_⟩
  · intro v
    change v ∈ Γ ↔ u (e.symm v) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
    rw [hΓ]
    constructor
    · rintro ⟨n, rfl⟩
      change u (e.symm (e (nativeRealChangedPeriodMap A b u (fun i => (n i : ℂ))))) ∈ _
      rw [e.symm_apply_apply, nativeRealChangedPeriodMap_integer, u.apply_symm_apply]
      exact ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_integer_mem b n
    · intro hv
      let w : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := ⟨u (e.symm v), hv⟩
      refine ⟨fun i => b.repr w i, ?_⟩
      change v = e (nativeRealChangedPeriodMap A b u (fun i => (b.repr w i : ℂ)))
      rw [nativeRealChangedPeriodMap_integer, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_repr]
      exact (congrArg e (u.symm_apply_apply (e.symm v))).trans (e.apply_symm_apply v) |>.symm
  · intro x y
    change H (e x) (e y) = H₀ x y
    rw [hH, e.symm_apply_apply, e.symm_apply_apply]

structure RealChangedAlgebraicModel where
  torus : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b)
  coordinates : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] Picard.ThetaConstruction.DefinitionsIntegral.Tangent g
  periods : ∀ z, torus.periodMap z = coordinates (nativeRealChangedPeriodMap A b u z)
  lattice : ∀ v, v ∈ torus.lattice ↔ u (coordinates.symm v) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
  form : ∀ x y, torus.riemannForm (coordinates x) (coordinates y) = Intrinsic.RiemannForm.nativeRiemannForm A L hL x y
  model : Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel torus

def realChangedAlgebraicModel : RealChangedAlgebraicModel A b u L hL := by
  apply Classical.choice
  obtain ⟨T, e, hp, hlat, hform⟩ := exists_nativeRealChangedPolarizedTorus A b u L hL hu
  exact ⟨T, e, hp, hlat, hform, Classical.choice (Picard.ThetaConstruction.PeriodModel.Geometric.exists_algebraicPeriodModel T)⟩

namespace RealChangedAlgebraicModel

variable {A b u L hL} (R : RealChangedAlgebraicModel A b u L hL)

def tangentEquiv : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel R.model.abelian :=
  R.coordinates.trans R.model.periodDifferential.toLinearEquiv

theorem tangentEquiv_lattice (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    R.tangentEquiv v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ↔ u v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := by
  have h := R.model.periodDifferential_lattice_iff (R.coordinates v)
  change R.tangentEquiv v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ↔ R.coordinates v ∈ R.torus.lattice at h
  rw [h, R.lattice, R.coordinates.symm_apply_apply]

def realPeriodEquiv : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel R.model.abelian :=
  u.symm.trans (R.tangentEquiv.restrictScalars ℝ)

theorem realPeriodEquiv_lattice (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
    R.realPeriodEquiv v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ↔ v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := by
  change R.tangentEquiv (u.symm v) ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ↔ _
  rw [R.tangentEquiv_lattice, u.apply_symm_apply]

def latticeEquiv : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A ≃ₗ[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian where
  toFun v := ⟨R.realPeriodEquiv v.val, (R.realPeriodEquiv_lattice v.val).mpr v.property⟩
  invFun w := ⟨R.realPeriodEquiv.symm w.val, (R.realPeriodEquiv_lattice _).mp
    ((R.realPeriodEquiv.apply_symm_apply w.val).symm ▸ w.property)⟩
  left_inv v := Subtype.ext (R.realPeriodEquiv.symm_apply_apply v.val)
  right_inv w := Subtype.ext (R.realPeriodEquiv.apply_symm_apply w.val)
  map_add' v w := Subtype.ext (R.realPeriodEquiv.map_add v.val w.val)
  map_smul' n v := Subtype.ext ((R.realPeriodEquiv.restrictScalars ℤ).map_smul n v.val)

theorem realPeriodEquiv_rational (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    R.realPeriodEquiv v.val ∈ Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian := by
  rcases v with ⟨v, hv⟩
  change R.realPeriodEquiv v ∈ Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ((R.realPeriodEquiv_lattice x).mpr hx)
  | zero => simpa only [map_zero] using (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian).zero_mem
  | add x y _ _ hx hy =>
    simpa only [map_add] using (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian).add_mem hx hy
  | smul q x _ hx =>
    exact (((R.realPeriodEquiv.restrictScalars ℚ).map_smul q x).symm) ▸
      (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian).smul_mem q hx

theorem realPeriodEquiv_symm_rational (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian) :
    R.realPeriodEquiv.symm v.val ∈ Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A := by
  rcases v with ⟨v, hv⟩
  change R.realPeriodEquiv.symm v ∈ Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A
  induction hv using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span ((R.realPeriodEquiv_lattice _).mp
      ((R.realPeriodEquiv.apply_symm_apply x).symm ▸ hx))
  | zero => simpa only [map_zero] using (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).zero_mem
  | add x y _ _ hx hy =>
    simpa only [map_add] using (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).add_mem hx hy
  | smul q x _ hx =>
    exact (((R.realPeriodEquiv.symm.restrictScalars ℚ).map_smul q x).symm) ▸
      (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).smul_mem q hx

def rationalMarking : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian where
  toFun v := ⟨R.realPeriodEquiv v.val, R.realPeriodEquiv_rational v⟩
  invFun v := ⟨R.realPeriodEquiv.symm v.val, R.realPeriodEquiv_symm_rational v⟩
  left_inv v := Subtype.ext (R.realPeriodEquiv.symm_apply_apply v.val)
  right_inv v := Subtype.ext (R.realPeriodEquiv.apply_symm_apply v.val)
  map_add' v w := Subtype.ext (R.realPeriodEquiv.map_add v.val w.val)
  map_smul' q v := Subtype.ext ((R.realPeriodEquiv.restrictScalars ℚ).map_smul q v.val)

theorem rationalMarking_integral (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    (R.rationalMarking v).val ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ↔ v.val ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A :=
  R.realPeriodEquiv_lattice v.val

theorem rationalMarking_projection (v : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection R.model.abelian (R.rationalMarking.baseChange ℚ ℂ _ _ v) =
      R.tangentEquiv (PeriodHodgeTransport.realChangedComplexPeriodMap A u v) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul z v =>
    change z • R.tangentEquiv (u.symm v.val) = R.tangentEquiv (z • u.symm v.val)
    exact (R.tangentEquiv.map_smul z (u.symm v.val)).symm

theorem rationalMarking_kernel :
    (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection R.model.abelian).ker.comap
      (R.rationalMarking.baseChange ℚ ℂ _ _).toLinearMap =
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker.map (PeriodHodgeTransport.realPeriodComplexification A u).toLinearMap := by
  rw [← PeriodHodgeTransport.realChangedComplexPeriodMap_kernel]
  ext v
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection R.model.abelian (R.rationalMarking.baseChange ℚ ℂ _ _ v) = 0 ↔
    PeriodHodgeTransport.realChangedComplexPeriodMap A u v = 0
  rw [R.rationalMarking_projection]
  exact map_eq_zero_iff R.tangentEquiv R.tangentEquiv.injective

end RealChangedAlgebraicModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.ChangedModel
