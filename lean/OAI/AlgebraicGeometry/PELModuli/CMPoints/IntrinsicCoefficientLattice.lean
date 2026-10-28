import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLattice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateLatticeQuotients

/-! # Intrinsic Coefficient Lattice -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientLattice

noncomputable section

section

/-! The native rational period marking in any coefficient-field rank.
Rank one applies to the full CM factors, while rank three applies to
the original PEL action. The lattice remains the actual exponential
period lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

section LatticeTransport

variable {E V : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V] {r : ℕ}

omit [NumberField E] in
theorem fullStableCoordinateLattice_map (Λ : Submodule ℤ V) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set V) = ⊤)
    (hstable : ∀ (a : NumberField.RingOfIntegers E) (v : V), v ∈ Λ → (a : E) • v ∈ Λ)
    (e : V ≃ₗ[E] (Fin r → E)) :
    CoordinateLattice.FullStableCoordinateLattice (Λ.map (e.restrictScalars ℤ).toLinearMap) := by
  refine ⟨hfg.map _, ?_, ?_⟩
  · change Submodule.span ℚ ((e.restrictScalars ℚ).toLinearMap '' (Λ : Set V)) = ⊤
    rw [← Submodule.map_span (e.restrictScalars ℚ).toLinearMap, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (e.restrictScalars ℚ).surjective
  · intro a x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨(a : E) • v, hstable a v hv, e.map_smul (a : E) v⟩

end LatticeTransport

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

local instance : IsIntegral (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.left := (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).variety.property

theorem native_field_finrank (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    Module.finrank E (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) = r := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  let : Module.Finite E (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
    Module.Finite.of_restrictScalars_finite ℚ E _
  have h := Module.finrank_mul_finrank ℚ E (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
  rw [AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank] at h
  have hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver.hom = g := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A
  have h' := h.trans (congrArg (fun n : ℕ => 2 * n) hd)
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := E)) (h'.trans hr.symm)

def coefficientCoordinates (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[E] (Fin r → E) := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  let : Module.Finite E (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
    Module.Finite.of_restrictScalars_finite ℚ E _
  exact ((Module.finBasis E (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))).reindex
    (finCongr (native_field_finrank A P ρ r hr))).equivFun

def coefficientMarkedLattice (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    Submodule ℤ (Fin r → E) := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  exact (AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).map
    ((coefficientCoordinates A P ρ r hr).restrictScalars ℤ).toLinearMap

theorem coefficientMarkedLattice_full_stable (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    CoordinateLattice.FullStableCoordinateLattice (coefficientMarkedLattice A P ρ r hr) := by
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  exact fullStableCoordinateLattice_map (AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods_fg _)
    (AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods_span _) (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.integralPeriods_stable A P ρ)
    (coefficientCoordinates A P ρ r hr)

end

/-! Compare the actual exponential lattice with its coefficient-field
marking, in every finite rank, and clear its integral denominators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem nativeCoefficientLatticeCoordinates_smul (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) (a : NumberField.RingOfIntegers E) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∀ x : IntrinsicLattice.nativeIntegerLattice A P ρ,
      coefficientCoordinates A P ρ r hr (IntrinsicLattice.nativeLatticeRationalPoint A P ρ (a • x)) =
        a • coefficientCoordinates A P ρ r hr (IntrinsicLattice.nativeLatticeRationalPoint A P ρ x) := by
  dsimp only
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  intro x
  rw [IntrinsicLattice.nativeLatticeRationalPoint_smul]
  exact (coefficientCoordinates A P ρ r hr).map_smul (a : E) _

theorem nativeCoefficientLatticeCoordinates_add (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∀ x y : IntrinsicLattice.nativeIntegerLattice A P ρ,
      coefficientCoordinates A P ρ r hr (IntrinsicLattice.nativeLatticeRationalPoint A P ρ (x + y)) =
        coefficientCoordinates A P ρ r hr (IntrinsicLattice.nativeLatticeRationalPoint A P ρ x) +
        coefficientCoordinates A P ρ r hr (IntrinsicLattice.nativeLatticeRationalPoint A P ρ y) := by
  dsimp only
  intro x y
  rw [IntrinsicLattice.nativeLatticeRationalPoint_add]
  exact (coefficientCoordinates A P ρ r hr).map_add
    (IntrinsicLattice.nativeLatticeRationalPoint A P ρ x) (IntrinsicLattice.nativeLatticeRationalPoint A P ρ y)

def nativeCoefficientLatticeCoordinates (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    IntrinsicLattice.nativeIntegerLattice A P ρ →ₗ[NumberField.RingOfIntegers E] (Fin r → E) := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let e := coefficientCoordinates A P ρ r hr
  exact
    { toFun := fun x => e (IntrinsicLattice.nativeLatticeRationalPoint A P ρ x)
      map_add' := nativeCoefficientLatticeCoordinates_add A P ρ r hr
      map_smul' := nativeCoefficientLatticeCoordinates_smul A P ρ r hr }

theorem nativeCoefficientLatticeCoordinates_apply (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) : let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∀ x : IntrinsicLattice.nativeIntegerLattice A P ρ,
      nativeCoefficientLatticeCoordinates A P ρ r hr x =
        coefficientCoordinates A P ρ r hr (IntrinsicLattice.nativeLatticeRationalPoint A P ρ x) := by
  dsimp only
  intro x
  rfl

def nativeCoefficientLatticeEquiv (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    IntrinsicLattice.nativeIntegerLattice A P ρ ≃ₗ[NumberField.RingOfIntegers E]
      CoordinateLattice.stableCoordinateLattice (coefficientMarkedLattice A P ρ r hr)
        (coefficientMarkedLattice_full_stable A P ρ r hr) := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let f := nativeCoefficientLatticeCoordinates A P ρ r hr
  let F := f.codRestrict
    (CoordinateLattice.stableCoordinateLattice (coefficientMarkedLattice A P ρ r hr)
      (coefficientMarkedLattice_full_stable A P ρ r hr))
    (fun x => ⟨⟨x.val, Submodule.subset_span x.property⟩, x.property,
      (nativeCoefficientLatticeCoordinates_apply A P ρ r hr x).symm⟩)
  apply LinearEquiv.ofBijective F
  constructor
  · intro x y h
    have he : f x = f y := congrArg Subtype.val h
    change nativeCoefficientLatticeCoordinates A P ρ r hr x =
      nativeCoefficientLatticeCoordinates A P ρ r hr y at he
    rw [nativeCoefficientLatticeCoordinates_apply, nativeCoefficientLatticeCoordinates_apply] at he
    exact IntrinsicLattice.nativeLatticeRationalPoint_injective A P ρ
      ((coefficientCoordinates A P ρ r hr).injective he)
  · intro y
    obtain ⟨v, hv, he⟩ := y.property
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (nativeCoefficientLatticeCoordinates_apply A P ρ r hr ⟨v.val, hv⟩).trans he

theorem exists_native_coefficient_lattice_bound (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ, q.Prime → D < q → ∀ n : ℕ,
      Nonempty (ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (IntrinsicLattice.nativeIntegerLattice A P ρ)
        (q ^ n) ≃ₗ[NumberField.RingOfIntegers E]
        (Fin r → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)))) := by
  dsimp only
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  obtain ⟨D, hD, hquot⟩ := CoordinateLatticeQuotients.exists_coordinate_quotient_bound
    (coefficientMarkedLattice A P ρ r hr) (coefficientMarkedLattice_full_stable A P ρ r hr)
  refine ⟨D, hD, fun q hq hb n => ?_⟩
  obtain ⟨e⟩ := hquot q hq hb n
  exact ⟨(ScalarQuotientMk.scalarQuotientCongr (nativeCoefficientLatticeEquiv A P ρ r hr) _).trans e⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientLattice
