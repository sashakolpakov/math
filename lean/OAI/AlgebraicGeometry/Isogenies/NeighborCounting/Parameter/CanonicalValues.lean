import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleLineSumCounts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ThreeParameterCounts

/-! # Canonical Values -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues

/-! Evaluate the original three finite parameter counts at the native
canonical targets, retaining both line permutations and repeated values. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ThreeParameterCounts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleLineSumCounts
open scoped BigOperators

variable {q : ℕ} [Fact q.Prime] {X : Type}
attribute [local instance] Classical.propDecidable
local instance : Fintype (Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) := Fintype.ofFinite _

def lineParameterValue (fallback : X) (f : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) : X :=
  if h : Module.finrank (ZMod q) U = 1 then f (e ⟨U, h⟩) else fallback

def canonicalParameterValue (x z xz : X)
    (y xy : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e e' : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (i : Fin 3) (U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) (flag : Bool) : X :=
  Fin.cases (if flag then x else lineParameterValue x y e U)
    (Fin.cases (if flag then lineParameterValue xz xy e' U else z) (fun _ => xz)) i

theorem canonicalParameterValue_zero (x z xz : X) (y xy : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e e' : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) (flag : Bool) :
    canonicalParameterValue x z xz y xy e e' 0 U flag =
      if flag then x else lineParameterValue x y e U := rfl

theorem canonicalParameterValue_one (x z xz : X) (y xy : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e e' : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) (flag : Bool) :
    canonicalParameterValue x z xz y xy e e' 1 U flag =
      if flag then lineParameterValue xz xy e' U else z := rfl

theorem canonicalParameterValue_two (x z xz : X) (y xy : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e e' : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) (flag : Bool) :
    canonicalParameterValue x z xz y xy e e' 2 U flag = xz := rfl

theorem lineParameterValue_line (fallback : X) (f : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    lineParameterValue fallback f e J.val = f (e J) := by
  simp only [lineParameterValue, dite_eq_left J.property]
  rfl

theorem lineParameterValue_sum (fallback : X) (f : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (∑ U : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q),
      if Module.finrank (ZMod q) U = 1 then
        ({lineParameterValue fallback f e U} : Multiset X) else 0) = AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset f := by
  apply EtaleLineSumCounts.line_sum_eq_of_equiv _ f e
  intro J
  simp only [lineParameterValue, dite_eq_left J.property]
  rfl

theorem original_canonical_parameter_counts
    (A : Fin 3 → Type) [∀ i, Fintype (A i)]
    (coordinates : ∀ i : Fin 3, A i ≃
      {J : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q × ZMod q) //
        Module.finrank (ZMod q) J = i.val + 1})
    (x z xz : X) (y xy : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → X)
    (e e' : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    ThreeParameterCounts.originalLabeledParameters A coordinates (canonicalParameterValue x z xz y xy e e') 0 =
      {x} + q • AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset y ∧
    ThreeParameterCounts.originalLabeledParameters A coordinates (canonicalParameterValue x z xz y xy e e') 1 =
      AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset xy + q ^ 2 • {z} ∧
    ThreeParameterCounts.originalLabeledParameters A coordinates (canonicalParameterValue x z xz y xy e e') 2 =
      {xz} := by
  have hdim : Module.finrank (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) = 2 := by simp
  have h := ThreeParameterCounts.original_three_parameter_counts A coordinates
    (canonicalParameterValue x z xz y xy e e') hdim
  simpa only [canonicalParameterValue_zero, canonicalParameterValue_one, canonicalParameterValue_two,
    Bool.false_eq_true, ↓reduceIte, lineParameterValue_sum,
    Nat.card_eq_fintype_card, ZMod.card] using h

end AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues.CoordinateCases

/-! The exhaustive projection and identity-flag cases of each original
rank-three coordinate parameter. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

variable {q : ℕ} [Fact q.Prime]
attribute [local instance] Classical.propDecidable

abbrev projection (J : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q × ZMod q)) :=
  J.map (LinearMap.fst (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) (ZMod q))

abbrev identityFlag (J : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q × ZMod q)) : Bool :=
  decide (SubspaceCounts.Construction.identityLine ≤ J)

theorem line_projection_cases (J : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q × ZMod q))
    (hJ : Module.finrank (ZMod q) J = 1) :
    (projection J = ⊥ ∧ identityFlag J = true) ∨
      ∃ L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q, projection J = L.val ∧ identityFlag J = false := by
  rcases SubspaceCounts.Construction.line_cases J hJ with h | ⟨hd, hdim⟩
  · left
    subst J
    constructor
    · apply le_antisymm ?_ bot_le
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      exact hw
    · exact decide_eq_true le_rfl
  · exact Or.inr ⟨⟨projection J, hdim⟩, rfl,
      decide_eq_false (SubspaceCounts.Construction.identityLine_not_le_of_disjoint J hd)⟩

theorem plane_projection_cases (J : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q × ZMod q))
    (hJ : Module.finrank (ZMod q) J = 2) :
    (∃ L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q, projection J = L.val ∧ identityFlag J = true) ∨
      (projection J = ⊤ ∧ identityFlag J = false) := by
  have hdim : Module.finrank (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) = 2 := by simp
  rcases SubspaceCounts.Construction.plane_cases hdim J hJ with ⟨hc, hr⟩ | ⟨hd, hp⟩
  · exact Or.inl ⟨⟨projection J, hr⟩, rfl, decide_eq_true hc⟩
  · exact Or.inr ⟨hp, decide_eq_false (SubspaceCounts.Construction.identityLine_not_le_of_disjoint J hd)⟩

theorem full_projection_case (J : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q × ZMod q))
    (hJ : Module.finrank (ZMod q) J = 3) :
    projection J = ⊤ ∧ identityFlag J = true := by
  have hdim : Module.finrank (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) = 2 := by simp
  have h := SubspaceCounts.Construction.full_kernel_unique hdim J hJ
  subst J
  simp [projection, identityFlag, LinearMap.range_eq_top.mpr LinearMap.fst_surjective]

end AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues.CoordinateCases

end

end OAI
