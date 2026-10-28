import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeBlocks
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeDivision

/-! # Intrinsic Lattice -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLattice

noncomputable section

/-! The native exponential lattice carries the actual integral PEL
action. Its rank-three E-marking gives an O_E-linear lattice isomorphism,
so the quotient-block cardinal calculation applies to the native lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

abbrev nativeAmbientModule : Module (NumberField.RingOfIntegers E) (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
  Module.compHom _ (AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ)

abbrev nativeAmbientScalarComm : let := nativeAmbientModule A P ρ
    SMulCommClass (NumberField.RingOfIntegers E) ℚ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) := by
  let := nativeAmbientModule A P ρ
  exact ⟨fun a b v => ((AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a).restrictScalars ℚ).map_smul b v⟩

def nativeIntegerLattice : let := nativeAmbientModule A P ρ
    Submodule (NumberField.RingOfIntegers E) (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) := by
  let := nativeAmbientModule A P ρ
  exact
    { carrier := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)
      zero_mem' := (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).zero_mem
      add_mem' := (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).add_mem
      smul_mem' := AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction_preserves A P ρ }

def nativeLatticeRationalPoint : let := nativeAmbientModule A P ρ
    nativeIntegerLattice A P ρ → AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) := by
  let := nativeAmbientModule A P ρ
  exact fun x => ⟨x.val, Submodule.subset_span x.property⟩

omit [NumberField E] [Algebra ℚ E] in
theorem nativeLatticeRationalPoint_add : let := nativeAmbientModule A P ρ
    ∀ x y : nativeIntegerLattice A P ρ,
      nativeLatticeRationalPoint A P ρ (x + y) =
        nativeLatticeRationalPoint A P ρ x + nativeLatticeRationalPoint A P ρ y := by
  dsimp only
  intro x y
  rfl

omit [NumberField E] [Algebra ℚ E] in
theorem nativeLatticeRationalPoint_injective : let := nativeAmbientModule A P ρ
    Function.Injective (nativeLatticeRationalPoint A P ρ) := by
  dsimp only
  intro x y h
  exact Subtype.ext (congrArg (fun v : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) => v.val) h)

theorem nativeLatticeRationalPoint_smul (a : NumberField.RingOfIntegers E) :
    let := nativeAmbientModule A P ρ
    ∀ x : nativeIntegerLattice A P ρ,
      nativeLatticeRationalPoint A P ρ (a • x) =
        AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ (a : E) (nativeLatticeRationalPoint A P ρ x) := by
  dsimp only
  let := nativeAmbientModule A P ρ
  intro x
  exact (AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A P ρ a (nativeLatticeRationalPoint A P ρ x)).symm

theorem nativeLatticeCoordinates_smul (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) (a : NumberField.RingOfIntegers E) :
    let := nativeAmbientModule A P ρ
    ∀ x : nativeIntegerLattice A P ρ,
      AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree (nativeLatticeRationalPoint A P ρ (a • x)) =
        a • AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree (nativeLatticeRationalPoint A P ρ x) := by
  dsimp only
  let := nativeAmbientModule A P ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  intro x
  rw [nativeLatticeRationalPoint_smul]
  exact (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree).map_smul (a : E) _

theorem nativeLatticeCoordinates_add (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let := nativeAmbientModule A P ρ
    ∀ x y : nativeIntegerLattice A P ρ,
      AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree (nativeLatticeRationalPoint A P ρ (x + y)) =
        AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree (nativeLatticeRationalPoint A P ρ x) +
        AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree (nativeLatticeRationalPoint A P ρ y) := by
  dsimp only
  intro x y
  rw [nativeLatticeRationalPoint_add]
  exact (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree).map_add
    (nativeLatticeRationalPoint A P ρ x) (nativeLatticeRationalPoint A P ρ y)

def nativeLatticeCoordinates (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let := nativeAmbientModule A P ρ
    nativeIntegerLattice A P ρ →ₗ[NumberField.RingOfIntegers E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := by
  let := nativeAmbientModule A P ρ
  let e := AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree
  exact
    { toFun := fun x => e (nativeLatticeRationalPoint A P ρ x)
      map_add' := nativeLatticeCoordinates_add A P ρ s hs hg hdegree
      map_smul' := nativeLatticeCoordinates_smul A P ρ s hs hg hdegree }

theorem nativeLatticeCoordinates_apply (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) : let := nativeAmbientModule A P ρ
    ∀ x : nativeIntegerLattice A P ρ,
      nativeLatticeCoordinates A P ρ s hs hg hdegree x =
        AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree (nativeLatticeRationalPoint A P ρ x) := by
  dsimp only
  intro x
  rfl

def nativeLatticeCoordinateEquiv (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let := nativeAmbientModule A P ρ
    nativeIntegerLattice A P ρ ≃ₗ[NumberField.RingOfIntegers E]
      LatticeComparison.stableIntegerLattice (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A P ρ s hs hg hdegree)
        (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A P ρ s hs hg hdegree) := by
  let := nativeAmbientModule A P ρ
  let f := nativeLatticeCoordinates A P ρ s hs hg hdegree
  let F := f.codRestrict
    (LatticeComparison.stableIntegerLattice (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A P ρ s hs hg hdegree)
      (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A P ρ s hs hg hdegree))
    (fun x => ⟨⟨x.val, Submodule.subset_span x.property⟩, x.property,
      (nativeLatticeCoordinates_apply A P ρ s hs hg hdegree x).symm⟩)
  apply LinearEquiv.ofBijective F
  constructor
  · intro x y h
    have he : f x = f y := congrArg Subtype.val h
    change nativeLatticeCoordinates A P ρ s hs hg hdegree x =
      nativeLatticeCoordinates A P ρ s hs hg hdegree y at he
    rw [nativeLatticeCoordinates_apply, nativeLatticeCoordinates_apply] at he
    exact nativeLatticeRationalPoint_injective A P ρ
      ((AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree).injective he)
  · intro y
    obtain ⟨v, hv, he⟩ := y.property
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (nativeLatticeCoordinates_apply A P ρ s hs hg hdegree ⟨v.val, hv⟩).trans he

theorem exists_native_lattice_bound (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let := nativeAmbientModule A P ρ
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ, q.Prime → D < q → ∀ n : ℕ,
      Nonempty (ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (nativeIntegerLattice A P ρ)
        (q ^ n) ≃ₗ[NumberField.RingOfIntegers E]
        (Fin 3 → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)))) := by
  dsimp only
  let := nativeAmbientModule A P ρ
  obtain ⟨D, hD, hquot⟩ := LatticeQuotients.exists_lattice_quotient_bound
    (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A P ρ s hs hg hdegree) (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A P ρ s hs hg hdegree)
  refine ⟨D, hD, fun q hq hb n => ?_⟩
  obtain ⟨e⟩ := hquot q hq hb n
  exact ⟨(ScalarQuotientMk.scalarQuotientCongr (nativeLatticeCoordinateEquiv A P ρ s hs hg hdegree) _).trans e⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLattice
