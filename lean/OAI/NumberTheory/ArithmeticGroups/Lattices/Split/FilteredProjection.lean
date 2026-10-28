import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredFactorInclusions
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorKernel

/-! # Filtered Projection -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredProjection.Construction

noncomputable section

/-! The split filtered subgroup projects continuously onto its
split exponential blocks, with kernel exactly the unipotent subgroup. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def splitFilteredToFilteredHom {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b w a hc →* FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b w where
  toFun g := ⟨g.val, ((FilteredBracketGroup.Construction.mem_splitFilteredBracketUnitGroup_iff B b w a hc g.val).mp g.property).2.choose⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

theorem splitFilteredToFilteredHom_continuous {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    Continuous (splitFilteredToFilteredHom B b w a hc) := continuous_subtype_val.subtype_mk _

def splitFilteredProjection {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b w a hc →* CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc :=
  ((FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b w).comp (splitFilteredToFilteredHom B b w a hc)).codRestrict
    (CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc) (fun g =>
      ((FilteredBracketGroup.Construction.mem_splitFilteredBracketUnitGroup_iff B b w a hc g.val).mp g.property).2.choose_spec)

theorem splitFilteredProjection_continuous {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    Continuous (splitFilteredProjection B b w a hc) :=
  ((FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection_continuous b w).comp
    (splitFilteredToFilteredHom_continuous B b w a hc)).subtype_mk _

theorem splitFilteredProjection_eq_one_iff {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L)
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y)
    (g : FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc) :
    splitFilteredProjection B b.toBasis w a hc g = 1 ↔ g.val ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B b w := by
  let q := splitFilteredToFilteredHom B b.toBasis w a hc g
  constructor
  · intro hg
    have he : FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w q = 1 := congrArg Subtype.val hg
    exact ⟨g.property.1, FilteredOperatorKernel.Construction.filtered_unit_mem_weightRaising_of_projection_one b w q he⟩
  · intro hg
    apply Subtype.ext
    exact UnipotentFilteredUnits.Construction.weightRaising_unit_blockProjection_eq_one b w q hg.2

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredProjection.Construction
