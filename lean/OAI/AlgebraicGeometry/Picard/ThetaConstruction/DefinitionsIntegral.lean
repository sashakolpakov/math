import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion
import OAI.NumberTheory.ArithmeticGroups.Period

/-! # Definitions Integral -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
section

/-!
Definitions from Statements/ThetaConstruction.lean, with unchanged mathematical content.
The positive-period and projectivity definitions are supplied by proved modules,
so no statement stub is imported. The analytic-model limitations of ThetaConstruction remain.
-/

open scoped BigOperators

abbrev Index (g : ℕ) := Fin (2 * g)
abbrev CVec (g : ℕ) := Index g → ℂ
abbrev Tangent (g : ℕ) := Fin g → ℂ
abbrev IntegralMatrix (g : ℕ) := Matrix (Index g) (Index g) ℤ

/-- Complexification of the fixed integral alternating form. -/
def pairing {g : ℕ} (E : IntegralMatrix g)
    (u v : CVec g) : ℂ :=
  ∑ i, ∑ j, u i * (E i j : ℂ) * v j

/-- Complexification of a fixed lattice endomorphism. -/
def matrixAction {g : ℕ} (M : IntegralMatrix g)
    (v : CVec g) : CVec g :=
  fun i => ∑ j, (M i j : ℂ) * v j

/--
The period is the kernel of the complexified marking.
The minus sign matches `PositivePeriod` with the convention
that the Riemann form is the imaginary part of a Hermitian
form conjugate-linear in its first variable.
-/
def CompatiblePositivePeriod {g : ℕ}
    (E : IntegralMatrix g) (P : Submodule ℂ (CVec g)) : Prop :=
  Geometry.ComplexBall.PrescribedSignsB.PositivePeriod g
    (fun u v => -pairing E u v)
    (fun u => star u) P

/--
Proposed analytic model of a marked polarized abelian variety.
The fixed matrix E records the polarization on the marked lattice.
No period-classification or endomorphism criterion is assumed here.
-/
structure MarkedPolarizedTorus (g : ℕ) (E : IntegralMatrix g) where
  periodMap : CVec g →ₗ[ℂ] Tangent g
  real_marking :
    Function.Bijective
      (fun x : Index g → ℝ => periodMap (fun i => (x i : ℂ)))
  lattice : AddSubgroup (Tangent g)
  lattice_marking :
    ∀ z, z ∈ lattice ↔
      ∃ n : Index g → ℤ,
        z = periodMap (fun i => (n i : ℂ))
  discrete : DiscreteTopology lattice
  compact : CompactSpace (Tangent g ⧸ lattice)
  projective : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus (Tangent g) lattice
  riemannForm :
    Tangent g →ₗ⋆[ℂ] Tangent g →ₗ[ℂ] ℂ
  hermitian :
    ∀ u v, riemannForm v u = star (riemannForm u v)
  positive :
    ∀ u, u ≠ 0 → 0 < (riemannForm u u).re
  polarization_marking :
    ∀ x y : Index g → ℝ,
      (riemannForm
        (periodMap (fun i => (x i : ℂ)))
        (periodMap (fun i => (y i : ℂ)))).im =
      (pairing E
        (fun i => (x i : ℂ))
        (fun i => (y i : ℂ))).re

/--
A complex-linear lift inducing M on the marked lattice.
Such a lift descends to a holomorphic group endomorphism
of the quotient torus.
-/
def InducesHolomorphicEndomorphism
    {g : ℕ} {E : IntegralMatrix g}
    (A : MarkedPolarizedTorus g E)
    (M : IntegralMatrix g) : Prop :=
  ∃ f : Tangent g →ₗ[ℂ] Tangent g,
    ∀ n : Index g → ℤ,
      f (A.periodMap (fun i => (n i : ℂ))) =
        A.periodMap
          (matrixAction M (fun i => (n i : ℂ)))

end

/-! An unconditional proof of the analytic formulation of ThetaConstruction. -/
open scoped BigOperators

variable {g : ℕ}

/-- Inclusion of the real marked homology in its complexification. -/
def realInclusion : (Index g → ℝ) →ₗ[ℝ] CVec g where
  toFun x i := (x i : ℂ)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [Complex.real_smul]

@[simp] lemma realInclusion_apply (x : Index g → ℝ) (i : Index g) :
    realInclusion x i = (x i : ℂ) := rfl

@[simp] lemma star_realInclusion (x : Index g → ℝ) :
    star (realInclusion x) = realInclusion x := by ext i; simp

lemma realInclusion_injective : Function.Injective (realInclusion (g := g)) := by
  intro x y h
  funext i
  exact Complex.ofReal_injective (congrFun h i)

/-- The integral form, bundled as a complex bilinear form. -/
def complexForm (E : IntegralMatrix g) : LinearMap.BilinForm ℂ (CVec g) :=
  Matrix.toBilin' (fun i j => (E i j : ℂ))

lemma complexForm_apply (E : IntegralMatrix g) (u v : CVec g) :
    complexForm E u v = pairing E u v := by
  exact Matrix.toBilin'_apply _ _ _

lemma pairing_star (E : IntegralMatrix g) (u v : CVec g) :
    star (pairing E u v) = pairing E (star u) (star v) := by
  simp [pairing]

lemma pairing_skew (E : IntegralMatrix g) (hE : E.transpose = -E)
    (u v : CVec g) : pairing E u v = -pairing E v u := by
  have he (i j : Index g) : E i j = -E j i := by
    have h := congrArg (fun M => M j i) hE
    exact h
  simp only [pairing, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [he j i]
  push_cast
  ring

lemma real_marking_of_positive (E : IntegralMatrix g)
    (P : Submodule ℂ (CVec g)) (hP : CompatiblePositivePeriod E P)
    (π : CVec g →ₗ[ℂ] Tangent g) (hπ : π.ker = P) :
    Function.Bijective ((π.restrictScalars ℝ).comp realInclusion) := by
  have hi : Function.Injective ((π.restrictScalars ℝ).comp realInclusion) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hp : realInclusion x ∈ P := by rw [← hπ]; exact hx
    by_contra hn
    have hne : realInclusion x ≠ 0 := by
      intro hz
      exact hn (realInclusion_injective (hz.trans (map_zero _).symm))
    have hpos := (hP.2.2.2.1 _ hp hne).2
    change 0 < (-pairing E (realInclusion x) (star (realInclusion x)) / Complex.I).re at hpos
    have hz : -pairing E (realInclusion x) (realInclusion x) = 0 := hP.2.2.1 _ hp _ hp
    rw [star_realInclusion, hz] at hpos
    simp at hpos
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  rw [← Module.finrank_mul_finrank ℝ ℂ (Tangent g)]
  simp [Index, Tangent, Nat.mul_comm]

lemma marked_lattice (π : CVec g →ₗ[ℂ] Tangent g)
    (hπ : Function.Bijective ((π.restrictScalars ℝ).comp realInclusion)) :
    ∃ Γ : AddSubgroup (Tangent g),
      (∀ z, z ∈ Γ ↔ ∃ n : Index g → ℤ,
        z = π (fun i => (n i : ℂ))) ∧
      DiscreteTopology Γ ∧ CompactSpace (Tangent g ⧸ Γ) := by
  let e := LinearEquiv.ofBijective ((π.restrictScalars ℝ).comp realInclusion) hπ
  let L₀ := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Index g)))
  have hL₀ (x : Index g → ℝ) : x ∈ L₀ ↔ ∃ n : Index g → ℤ,
      x = fun i => (n i : ℝ) := by
    rw [(Pi.basisFun ℝ (Index g)).mem_span_iff_repr_mem ℤ]
    simp only [Pi.basisFun_repr]
    constructor
    · intro h
      choose n hn using h
      exact ⟨n, funext (fun i => (hn i).symm)⟩
    · rintro ⟨n, rfl⟩
      exact fun i => ⟨n i, rfl⟩
  let L := ZLattice.comap ℝ L₀ e.symm.toContinuousLinearEquiv.toLinearMap
  let Γ := L.toAddSubgroup
  have hmem (z : Tangent g) : z ∈ Γ ↔ ∃ n : Index g → ℤ,
      z = π (fun i => (n i : ℂ)) := by
    change e.symm z ∈ L₀ ↔ _
    rw [hL₀]
    apply exists_congr
    intro n
    rw [e.symm_apply_eq]
    rfl
  have hd : DiscreteTopology Γ := inferInstanceAs (DiscreteTopology L)
  have hc : CompactSpace (Tangent g ⧸ Γ) := by
    apply isCompact_univ_iff.mp
    have h := IsZLattice.isCompact_range_of_periodic L
      (QuotientAddGroup.mk : Tangent g → Tangent g ⧸ Γ)
      QuotientAddGroup.continuous_mk (by
        intro z w hw
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
    rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at h
  exact ⟨Γ, hmem, hd, hc⟩

/-- Construction of a marked polarized torus from a positive period. -/
theorem realize_positive_period (E : IntegralMatrix g)
    (hE : E.transpose = -E) (P : Submodule ℂ (CVec g))
    (hP : CompatiblePositivePeriod E P) :
    ∃ A : MarkedPolarizedTorus g E, A.periodMap.ker = P := by
  let κ : CVec g ≃ₗ⋆[ℂ] CVec g := starLinearEquiv ℂ
  let Ψ := -complexForm E
  have hperiod : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod g (fun x y => Ψ x y) κ P := by
    change Geometry.ComplexBall.PrescribedSignsB.PositivePeriod g (fun x y => -complexForm E x y) (fun x => star x) P
    simpa only [CompatiblePositivePeriod, complexForm_apply] using hP
  have hreal (x y : CVec g) : star (Ψ x y) = Ψ (κ x) (κ y) := by
    simp only [Ψ, LinearMap.neg_apply, complexForm_apply, κ,
      starLinearEquiv_apply, star_neg, pairing_star]
  have hskew (x y : CVec g) : Ψ x y = -Ψ y x := by
    simp only [Ψ, LinearMap.neg_apply, complexForm_apply, neg_neg]
    exact neg_eq_iff_eq_neg.mpr (pairing_skew E hE x y)
  obtain ⟨π, H, hk, hs, hsym, hpos, hriem⟩ :=
    NumberTheory.ArithmeticGroups.Period.CongruenceLevel.exists_positive_quotient κ (fun x => star_star x) Ψ P g hperiod hreal hskew
  have hbij := real_marking_of_positive E P hP π hk
  obtain ⟨Γ, hΓ, hdisc, hcompact⟩ := marked_lattice π hbij
  have hmark (x y : Index g → ℝ) :
      (H (π (fun i => (x i : ℂ))) (π (fun i => (y i : ℂ)))).im =
      (pairing E (fun i => (x i : ℂ)) (fun i => (y i : ℂ))).re := by
    have h := hriem (realInclusion x) (realInclusion y)
      (star_realInclusion x) (star_realInclusion y)
    simpa [Ψ, complexForm_apply, realInclusion] using h
  have hint : ∀ u ∈ Γ, ∀ v ∈ Γ, ∃ m : ℤ, (H u v).im = (m : ℝ) := by
    intro u hu v hv
    obtain ⟨n, rfl⟩ := (hΓ u).mp hu
    obtain ⟨m, rfl⟩ := (hΓ v).mp hv
    refine ⟨∑ i, ∑ j, n i * E i j * m j, ?_⟩
    have h := hmark (fun i => (n i : ℝ)) (fun i => (m i : ℝ))
    simpa [pairing] using h
  let : DiscreteTopology Γ := hdisc
  let : CompactSpace (Tangent g ⧸ Γ) := hcompact
  exact ⟨{
    periodMap := π
    real_marking := hbij
    lattice := Γ
    lattice_marking := hΓ
    discrete := hdisc
    compact := hcompact
    projective := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (Tangent g) Γ).mpr
      ⟨H, hsym, hpos, hint⟩
    riemannForm := H
    hermitian := hsym
    positive := hpos
    polarization_marking := hmark }, hk⟩

lemma periodMap_surjective {E : IntegralMatrix g} (A : MarkedPolarizedTorus g E) :
    Function.Surjective A.periodMap := by
  intro z
  obtain ⟨x, hx⟩ := A.real_marking.2 z
  exact ⟨_, hx⟩

lemma realInclusion_basis (i : Index g) :
    realInclusion ((Pi.basisFun ℝ (Index g)) i) = (Pi.basisFun ℂ (Index g)) i := by
  ext j
  by_cases h : j = i <;> simp [Pi.basisFun_apply, h]

lemma pairing_real (E : IntegralMatrix g) (x y : Index g → ℝ) :
    ((pairing E (realInclusion x) (realInclusion y)).re : ℂ) =
      pairing E (realInclusion x) (realInclusion y) := by
  simp [pairing, realInclusion]

/-- Recover the complexified Riemann form from the marked Hermitian form. -/
lemma polarization_identity {E : IntegralMatrix g} (A : MarkedPolarizedTorus g E)
    (u v : CVec g) :
    (2 * Complex.I) * pairing E u v =
      A.riemannForm (A.periodMap (star u)) (A.periodMap v) -
      A.riemannForm (A.periodMap (star v)) (A.periodMap u) := by
  let B : LinearMap.BilinForm ℂ (CVec g) :=
    (A.riemannForm.comp (A.periodMap.comp (starLinearEquiv ℂ).toLinearMap)).compl₂
      A.periodMap
  have hB (x y : CVec g) : B x y =
      A.riemannForm (A.periodMap (star x)) (A.periodMap y) := rfl
  have hflip (x y : CVec g) : B.flip x y = B y x := rfl
  have heq : (2 * Complex.I) • complexForm E = B - B.flip := by
    apply (Pi.basisFun ℂ (Index g)).ext
    intro i
    apply (Pi.basisFun ℂ (Index g)).ext
    intro j
    rw [← realInclusion_basis i, ← realInclusion_basis j]
    simp only [LinearMap.smul_apply, smul_eq_mul, complexForm_apply,
      LinearMap.sub_apply, hflip, hB]
    rw [star_realInclusion, star_realInclusion]
    rw [Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew A.riemannForm A.hermitian]
    have hm := A.polarization_marking ((Pi.basisFun ℝ (Index g)) i)
      ((Pi.basisFun ℝ (Index g)) j)
    have hm' : (A.riemannForm
        (A.periodMap (realInclusion ((Pi.basisFun ℝ (Index g)) i)))
        (A.periodMap (realInclusion ((Pi.basisFun ℝ (Index g)) j)))).im =
        (pairing E (realInclusion ((Pi.basisFun ℝ (Index g)) i))
          (realInclusion ((Pi.basisFun ℝ (Index g)) j))).re := hm
    rw [hm', pairing_real]
  have h := congrArg (fun D : LinearMap.BilinForm ℂ (CVec g) => D u v) heq
  simpa only [LinearMap.smul_apply, smul_eq_mul, complexForm_apply,
    LinearMap.sub_apply, hflip, hB] using h

lemma complexForm_nondegenerate (E : IntegralMatrix g) (hE : E.det ≠ 0) :
    (complexForm E).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
  have h : (E.det : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hE
  rw [Int.cast_det] at h
  convert h using 1
  congr 1

lemma kernel_star_zero {E : IntegralMatrix g} (hE : E.det ≠ 0)
    (A : MarkedPolarizedTorus g E) (u : CVec g)
    (hu : A.periodMap u = 0) (hs : A.periodMap (star u) = 0) : u = 0 := by
  apply (complexForm_nondegenerate E hE).1 u
  intro v
  have h := polarization_identity A u v
  rw [hu, hs] at h
  simp only [map_zero, LinearMap.zero_apply, sub_zero] at h
  have hz : pairing E u v = 0 :=
    (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  rwa [complexForm_apply]

def conjugatePeriodMap {E : IntegralMatrix g} (A : MarkedPolarizedTorus g E) :
    CVec g →ₗ[ℂ] Tangent g where
  toFun u := star (A.periodMap (star u))
  map_add' u v := by simp
  map_smul' a u := by simp

@[simp] lemma conjugatePeriodMap_apply {E : IntegralMatrix g}
    (A : MarkedPolarizedTorus g E) (u : CVec g) :
    conjugatePeriodMap A u = star (A.periodMap (star u)) := rfl

lemma kernel_finrank {E : IntegralMatrix g} (A : MarkedPolarizedTorus g E) :
    Module.finrank ℂ A.periodMap.ker = g := by
  have h := A.periodMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (periodMap_surjective A)] at h
  have hT : Module.finrank ℂ (⊤ : Submodule ℂ (Tangent g)) = g := by simp [Tangent]
  have hV : Module.finrank ℂ (CVec g) = 2 * g := by simp [CVec, Index]
  rw [hT, hV] at h
  omega

lemma kernel_quotient_finrank {E : IntegralMatrix g} (A : MarkedPolarizedTorus g E) :
    Module.finrank ℂ (CVec g ⧸ A.periodMap.ker) = g := by
  have h := (A.periodMap.quotKerEquivOfSurjective (periodMap_surjective A)).finrank_eq
  simpa [Tangent] using h

lemma conjugatePeriodMap_kernel_bijective {E : IntegralMatrix g} (hE : E.det ≠ 0)
    (A : MarkedPolarizedTorus g E) :
    Function.Bijective ((conjugatePeriodMap A).domRestrict A.periodMap.ker) := by
  have hi : Function.Injective ((conjugatePeriodMap A).domRestrict A.periodMap.ker) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    apply Subtype.ext
    apply kernel_star_zero hE A u u.property
    change star (A.periodMap (star (u : CVec g))) = 0 at hu
    exact star_eq_zero.mp hu
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  rw [kernel_finrank]
  simp [Tangent]

lemma kernel_conjugate_splitting {E : IntegralMatrix g} (hE : E.det ≠ 0)
    (A : MarkedPolarizedTorus g E) (x : CVec g) :
    ∃! uv : CVec g × CVec g,
      uv.1 ∈ A.periodMap.ker ∧ uv.2 ∈ A.periodMap.ker ∧
        x = uv.1 + star uv.2 := by
  obtain ⟨u, hu⟩ := (conjugatePeriodMap_kernel_bijective hE A).2
    (conjugatePeriodMap A x)
  let v := star (x - (u : CVec g))
  have hv : v ∈ A.periodMap.ker := by
    change A.periodMap (star (x - (u : CVec g))) = 0
    rw [star_sub, map_sub, sub_eq_zero]
    have h := congrArg star hu
    simpa only [LinearMap.domRestrict_apply, conjugatePeriodMap_apply, star_star] using h.symm
  have hsum : x = (u : CVec g) + star v := by simp [v]
  refine ⟨((u : CVec g), v), ⟨u.property, hv, hsum⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  have hφ (c d : CVec g) (hd : d ∈ A.periodMap.ker) :
      conjugatePeriodMap A (c + star d) = conjugatePeriodMap A c := by
    change A.periodMap d = 0 at hd
    simp [conjugatePeriodMap, hd]
  have hau : a = (u : CVec g) := by
    have h := (conjugatePeriodMap_kernel_bijective hE A).1
      (a₁ := ⟨a, ha⟩) (a₂ := u)
      (show conjugatePeriodMap A a = conjugatePeriodMap A u from by
        rw [← hφ a b hb, ← hab]
        exact hu.symm)
    exact congrArg Subtype.val h
  apply Prod.ext hau
  have h : star b = star v := by
    rw [hau] at hab
    exact add_left_cancel (hab.symm.trans hsum)
  exact star_injective h

lemma kernel_isotropic {E : IntegralMatrix g} (A : MarkedPolarizedTorus g E)
    (u : CVec g) (hu : u ∈ A.periodMap.ker)
    (v : CVec g) (hv : v ∈ A.periodMap.ker) : -pairing E u v = 0 := by
  have h := polarization_identity A u v
  change A.periodMap u = 0 at hu
  change A.periodMap v = 0 at hv
  rw [hu, hv] at h
  simp only [map_zero, sub_zero] at h
  have hz := (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  exact neg_eq_zero.mpr hz

lemma kernel_positive {E : IntegralMatrix g} (hE : E.det ≠ 0)
    (A : MarkedPolarizedTorus g E) (u : CVec g)
    (hu : u ∈ A.periodMap.ker) (hne : u ≠ 0) :
    (-pairing E u (star u) / Complex.I).im = 0 ∧
      0 < (-pairing E u (star u) / Complex.I).re := by
  change A.periodMap u = 0 at hu
  have hs : A.periodMap (star u) ≠ 0 := fun h => hne (kernel_star_zero hE A u hu h)
  have h := polarization_identity A u (star u)
  rw [star_star, hu] at h
  simp only [map_zero, sub_zero] at h
  have hid : -pairing E u (star u) / Complex.I =
      A.riemannForm (A.periodMap (star u)) (A.periodMap (star u)) / 2 := by
    calc
      _ = ((2 * Complex.I) * pairing E u (star u)) / 2 := by
        rw [Complex.div_I]
        ring
      _ = _ := congrArg (fun z : ℂ => z / 2) h
  rw [hid, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_self_eq_real A.riemannForm A.hermitian]
  constructor
  · simp
  · simpa using div_pos (A.positive _ hs) (by norm_num : (0 : ℝ) < 2)

/-- Every marked polarized torus has a compatible positive period. -/
theorem period_positive {E : IntegralMatrix g} (hE : E.det ≠ 0)
    (A : MarkedPolarizedTorus g E) : CompatiblePositivePeriod E A.periodMap.ker := by
  exact ⟨kernel_finrank A, kernel_quotient_finrank A, kernel_isotropic A,
    kernel_positive hE A, kernel_conjugate_splitting hE A⟩

section LinearDescent
variable {V T S : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup T] [Module ℂ T] [AddCommGroup S] [Module ℂ S]

/-- A linear map constant on the fibers of a surjection descends uniquely. -/
lemma exists_descended_map (π : V →ₗ[ℂ] T) (hs : Function.Surjective π)
    (τ : V →ₗ[ℂ] S) (hk : π.ker ≤ τ.ker) :
    ∃ f : T →ₗ[ℂ] S, ∀ v, f (π v) = τ v := by
  let f := (π.ker.liftQ τ hk).comp (π.quotKerEquivOfSurjective hs).symm.toLinearMap
  refine ⟨f, fun v => ?_⟩
  simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

end LinearDescent

/-- Period kernels classify the marked complex tori. -/
theorem period_eq_iff_isomorphic {E : IntegralMatrix g}
    (A B : MarkedPolarizedTorus g E) :
    A.periodMap.ker = B.periodMap.ker ↔
      ∃ e : Tangent g ≃ₗ[ℂ] Tangent g,
        ∀ v, e (A.periodMap v) = B.periodMap v := by
  constructor
  · intro hk
    obtain ⟨f, hf⟩ := exists_descended_map A.periodMap (periodMap_surjective A)
      B.periodMap hk.le
    have hi : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro z hz
      obtain ⟨v, rfl⟩ := periodMap_surjective A z
      have hv : v ∈ B.periodMap.ker := (hf v).symm.trans hz
      rw [← hk] at hv
      exact hv
    have hs : Function.Surjective f := by
      intro z
      obtain ⟨v, rfl⟩ := periodMap_surjective B z
      exact ⟨A.periodMap v, hf v⟩
    exact ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, hf⟩
  · rintro ⟨e, he⟩
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv
      rw [← he v, hv, map_zero]
    · intro hv
      apply e.injective
      rw [he, hv, map_zero]

def complexEnd (M : IntegralMatrix g) : CVec g →ₗ[ℂ] CVec g :=
  Matrix.mulVecLin (fun i j => (M i j : ℂ))

@[simp] lemma complexEnd_apply (M : IntegralMatrix g) (v : CVec g) :
    complexEnd M v = matrixAction M v := rfl

lemma integralInclusion_basis (i : Index g) :
    (fun j => (((Pi.basisFun ℤ (Index g)) i) j : ℂ)) =
      (Pi.basisFun ℂ (Index g)) i := by
  ext j
  by_cases h : j = i <;> simp [Pi.basisFun_apply, h]

/-- Integral basis vectors suffice to test equality of complex-linear maps. -/
lemma linearMap_eq_of_integral_values
    (f k : CVec g →ₗ[ℂ] Tangent g)
    (h : ∀ n : Index g → ℤ, f (fun i => (n i : ℂ)) = k (fun i => (n i : ℂ))) :
    f = k := by
  apply (Pi.basisFun ℂ (Index g)).ext
  intro i
  have hi := h ((Pi.basisFun ℤ (Index g)) i)
  simpa only [integralInclusion_basis] using hi

/-- Holomorphic descent is precisely preservation of the period kernel. -/
theorem endomorphism_iff {E : IntegralMatrix g}
    (A : MarkedPolarizedTorus g E) (M : IntegralMatrix g) :
    InducesHolomorphicEndomorphism A M ↔
      ∀ v ∈ A.periodMap.ker, matrixAction M v ∈ A.periodMap.ker := by
  constructor
  · rintro ⟨f, hf⟩
    have heq : f.comp A.periodMap = A.periodMap.comp (complexEnd M) :=
      linearMap_eq_of_integral_values _ _ hf
    intro v hv
    change A.periodMap v = 0 at hv
    have h := congrArg (fun k : CVec g →ₗ[ℂ] Tangent g => k v) heq
    change f (A.periodMap v) = A.periodMap (matrixAction M v) at h
    rw [hv, map_zero] at h
    exact h.symm
  · intro h
    obtain ⟨f, hf⟩ := exists_descended_map A.periodMap (periodMap_surjective A)
      (A.periodMap.comp (complexEnd M)) h
    exact ⟨f, fun n => hf (fun i => (n i : ℂ))⟩

/-- ThetaConstruction, with the hypotheses and conclusion of the committed specification. -/
theorem siegel_period_uniformization
    (g : ℕ)
    (E : IntegralMatrix g)
    (hE_alternating : E.transpose = -E)
    (hE_nondegenerate : E.det ≠ 0) :
    (∀ P : Submodule ℂ (CVec g),
      CompatiblePositivePeriod E P ↔
        ∃ A : MarkedPolarizedTorus g E, A.periodMap.ker = P) ∧
    (∀ A B : MarkedPolarizedTorus g E,
      A.periodMap.ker = B.periodMap.ker ↔
        ∃ e : Tangent g ≃ₗ[ℂ] Tangent g,
          ∀ v, e (A.periodMap v) = B.periodMap v) ∧
    (∀ (A : MarkedPolarizedTorus g E) (M : IntegralMatrix g),
      InducesHolomorphicEndomorphism A M ↔
        ∀ v ∈ A.periodMap.ker,
          matrixAction M v ∈ A.periodMap.ker) := by
  refine ⟨?_, period_eq_iff_isomorphic, endomorphism_iff⟩
  intro P
  constructor
  · exact realize_positive_period E hE_alternating P
  · rintro ⟨A, rfl⟩
    exact period_positive hE_nondegenerate A

end AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral

namespace AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral.Geometric

/-! The original integral marking and alternating form on the constructed
period lattice. These data permit a semicharacter for the original
polarization, rather than only for a multiple of it. -/

open scoped BigOperators

variable {g : ℕ} {E : IntegralMatrix g}

def integerCoordinates : (Index g → ℤ) →ₗ[ℤ] CVec g where
  toFun n i := (n i : ℂ)
  map_add' n m := by ext i; simp
  map_smul' a n := by ext i; simp

def integralProjection (T : MarkedPolarizedTorus g E) :
    (Index g → ℤ) →ₗ[ℤ] T.lattice where
  toFun n := ⟨T.periodMap (integerCoordinates n),
    (T.lattice_marking _).mpr ⟨n, rfl⟩⟩
  map_add' n m := by
    apply Subtype.ext
    change T.periodMap (integerCoordinates (n + m)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a n := by
    apply Subtype.ext
    change T.periodMap (integerCoordinates (a • n)) = a • T.periodMap (integerCoordinates n)
    rw [map_smul]
    exact map_zsmul T.periodMap a (integerCoordinates n)

lemma integralProjection_bijective (T : MarkedPolarizedTorus g E) :
    Function.Bijective (integralProjection T) := by
  constructor
  · intro n m h
    have hC := congrArg Subtype.val h
    have hR : T.periodMap (fun i => ((n i : ℝ) : ℂ)) =
        T.periodMap (fun i => ((m i : ℝ) : ℂ)) := by
      simpa [integralProjection, integerCoordinates] using hC
    have he := T.real_marking.1 hR
    funext i
    exact Int.cast_injective (congrFun he i)
  · intro l
    obtain ⟨n, hn⟩ := (T.lattice_marking l.val).mp l.property
    exact ⟨n, Subtype.ext hn.symm⟩

def integralMarkingEquiv (T : MarkedPolarizedTorus g E) :
    (Index g → ℤ) ≃ₗ[ℤ] T.lattice :=
  LinearEquiv.ofBijective (integralProjection T) (integralProjection_bijective T)

def integralLatticeBasis (T : MarkedPolarizedTorus g E) :
    Module.Basis (Index g) ℤ T.lattice :=
  (Pi.basisFun ℤ (Index g)).map (integralMarkingEquiv T)

def integralLatticeForm (T : MarkedPolarizedTorus g E) :
    LinearMap.BilinForm ℤ T.lattice :=
  (Matrix.toBilin' E).compl₁₂ (integralMarkingEquiv T).symm.toLinearMap
    (integralMarkingEquiv T).symm.toLinearMap

lemma integerBilin_skew (E : IntegralMatrix g) (hE : E.transpose = -E)
    (x y : Index g → ℤ) :
    Matrix.toBilin' E x y = -Matrix.toBilin' E y x := by
  have he (i j : Index g) : E i j = -E j i :=
    congrArg (fun M => M j i) hE
  simp only [Matrix.toBilin'_apply, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [he j i]
  ring

lemma integralLatticeForm_isAlt (T : MarkedPolarizedTorus g E)
    (hE : E.transpose = -E) : (integralLatticeForm T).IsAlt := by
  intro l
  change Matrix.toBilin' E ((integralMarkingEquiv T).symm l)
    ((integralMarkingEquiv T).symm l) = 0
  have h := integerBilin_skew E hE ((integralMarkingEquiv T).symm l)
    ((integralMarkingEquiv T).symm l)
  omega

lemma integralMarkingEquiv_period (T : MarkedPolarizedTorus g E) (l : T.lattice) :
    T.periodMap (integerCoordinates ((integralMarkingEquiv T).symm l)) = l.val :=
  congrArg Subtype.val ((integralMarkingEquiv T).apply_symm_apply l)

lemma integralLatticeForm_riemann (T : MarkedPolarizedTorus g E) (l m : T.lattice) :
    (T.riemannForm l.val m.val).im = (integralLatticeForm T l m : ℝ) := by
  let n := (integralMarkingEquiv T).symm l
  let k := (integralMarkingEquiv T).symm m
  have hn : T.periodMap (fun i => (n i : ℂ)) = l.val := integralMarkingEquiv_period T l
  have hk : T.periodMap (fun i => (k i : ℂ)) = m.val := integralMarkingEquiv_period T m
  have h := T.polarization_marking (fun i => (n i : ℝ)) (fun i => (k i : ℝ))
  have h' : (T.riemannForm (T.periodMap (fun i => (n i : ℂ)))
      (T.periodMap (fun i => (k i : ℂ)))).im =
      (Matrix.toBilin' E n k : ℝ) := by
    simpa [pairing, Matrix.toBilin'_apply] using h
  rw [hn, hk] at h'
  exact h'

end AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral.Geometric

end

end OAI
