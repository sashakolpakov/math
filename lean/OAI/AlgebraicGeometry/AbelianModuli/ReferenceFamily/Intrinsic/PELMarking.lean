import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum

/-! # PEL Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking

noncomputable section

/-! A native complex PEL abelian scheme has a constructed rank-three
E-marking of its rational periods. The image of its actual integral
period lattice is finitely generated, rationally full and O_E-stable. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction

section Transport

variable {E V : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]

omit [NumberField E] in
theorem fullStableLattice_map (Λ : Submodule ℤ V) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set V) = ⊤)
    (hstable : ∀ (a : NumberField.RingOfIntegers E) (v : V), v ∈ Λ → (a : E) • v ∈ Λ)
    (e : V ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice (Λ.map (e.restrictScalars ℤ).toLinearMap) := by
  refine ⟨hfg.map _, ?_, ?_⟩
  · change Submodule.span ℚ ((e.restrictScalars ℚ).toLinearMap '' (Λ : Set V)) = ⊤
    rw [← Submodule.map_span (e.restrictScalars ℚ).toLinearMap, hspan,
      Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (e.restrictScalars ℚ).surjective
  · intro a x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨(a : E) • v, hstable a v hv, e.map_smul (a : E) v⟩

end Transport

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem integralPeriods_stable (a : NumberField.RingOfIntegers E)
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (hv : v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    (a : E) • v ∈ RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  change (NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ (a : E) v).val ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)
  exact (congrArg (fun w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) => w.val ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
    (NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A P ρ a v)).mpr (IntegralAction.IntrinsicIntegralAction.linearAction_preserves A P ρ a v.val hv)

def coordinates (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
    RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  let : Module.Finite E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
    Module.Finite.of_restrictScalars_finite ℚ E _
  exact ((Module.finBasis E (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))).reindex
    (finCongr (NumberFieldAction.IntrinsicNumberFieldAction.field_finrank_three A P ρ s hs hg hdegree))).equivFun

def markedLattice (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  exact (RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).map
    ((coordinates A P ρ s hs hg hdegree).restrictScalars ℤ).toLinearMap

theorem markedLattice_full_stable (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice (markedLattice A P ρ s hs hg hdegree) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A P ρ
  exact fullStableLattice_map (RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (RationalLattice.IntrinsicRationalPeriods.integralPeriods_fg _)
    (RationalLattice.IntrinsicRationalPeriods.integralPeriods_span _) (integralPeriods_stable A P ρ) (coordinates A P ρ s hs hg hdegree)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking
