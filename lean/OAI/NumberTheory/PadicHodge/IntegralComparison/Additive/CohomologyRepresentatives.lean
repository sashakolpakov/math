import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Cohomology Representatives -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CohomologyRepresentatives

noncomputable section

/-! Cocycles and boundaries for the actual categorical cohomology of
complexes of abelian groups, in arbitrary universe. The quotient
identification is mathlib's canonical short-complex homology isomorphism. -/

open _root_.CategoryTheory

universe u

variable (C : CochainComplex AddCommGrpCat.{u} ℕ)

abbrev cocycles (n : ℕ) : AddSubgroup (C.X n) := (C.sc n).g.hom.ker

abbrev boundaryMap (n : ℕ) : (C.sc n).X₁ →+ cocycles C n := (C.sc n).abToCycles

abbrev boundaries (n : ℕ) : AddSubgroup (cocycles C n) := (boundaryMap C n).range

def quotientEquiv (n : ℕ) : C.homology n ≃+ (cocycles C n ⧸ boundaries C n) :=
  (C.sc n).abHomologyIso.addCommGroupIsoToAddEquiv

def cohomologyClass (n : ℕ) : cocycles C n →+ C.homology n :=
  (quotientEquiv C n).symm.toAddMonoidHom.comp (QuotientAddGroup.mk' (boundaries C n))

theorem mem_cocycles_iff (n : ℕ) (x : C.X n) :
    x ∈ cocycles C n ↔ C.d n (n + 1) x = 0 := by
  change C.d n ((ComplexShape.up ℕ).next n) x = 0 ↔ _
  rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]

theorem class_surjective (n : ℕ) : Function.Surjective (cohomologyClass C n) :=
  (quotientEquiv C n).symm.surjective.comp (QuotientAddGroup.mk'_surjective _)

theorem class_eq_zero_iff (n : ℕ) (x : cocycles C n) :
    cohomologyClass C n x = 0 ↔ x ∈ boundaries C n := by
  change (quotientEquiv C n).symm ((QuotientAddGroup.mk' (boundaries C n)) x) = 0 ↔ _
  rw [← (quotientEquiv C n).symm.map_zero, (quotientEquiv C n).symm.injective.eq_iff]
  exact QuotientAddGroup.eq_zero_iff x

theorem class_boundary_zero (n : ℕ) (x : (C.sc n).X₁) :
    cohomologyClass C n (boundaryMap C n x) = 0 :=
  (class_eq_zero_iff C n _).mpr ⟨x, rfl⟩

theorem class_eq_iff (n : ℕ) (x y : cocycles C n) :
    cohomologyClass C n x = cohomologyClass C n y ↔ x - y ∈ boundaries C n := by
  rw [← sub_eq_zero, ← map_sub, class_eq_zero_iff]

theorem class_eq_zero_iff_exists_succ (n : ℕ) (x : cocycles C (n + 1)) :
    cohomologyClass C (n + 1) x = 0 ↔
      ∃ z : C.X n, C.d n (n + 1) z = (x : C.X (n + 1)) := by
  rw [class_eq_zero_iff]
  have he : x ∈ boundaries C (n + 1) ↔
      ∃ z : (C.sc (n + 1)).X₁, (C.sc (n + 1)).f z = (x : C.X (n + 1)) := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, congrArg Subtype.val hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
  rw [he]
  change (∃ z : C.X ((ComplexShape.up ℕ).prev (n + 1)),
    C.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) z = (x : C.X (n + 1))) ↔ _
  rw [(ComplexShape.up ℕ).prev_eq'
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CohomologyRepresentatives
