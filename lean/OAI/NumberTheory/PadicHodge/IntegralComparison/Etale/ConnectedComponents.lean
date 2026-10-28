import OAI.NumberTheory.PadicHodge.IntegralComparison.ConnectedComponentSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DegreeZeroPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial

/-! # Connected Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedComponents

noncomputable section

/-! The original rational pro-étale degree-zero cohomology and its automorphisms in component coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDegreeZero

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [NoetherianSpace X]

local instance : TotallyDisconnectedSpace (Cohomology.Coeff.{u} ℓ) :=
  (Homeomorph.ulift.isEmbedding.isTotallyDisconnected_range).mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

def equiv : Cohomology.RationalEllAdicCohomology ℓ X 0 ≃ₗ[ℚ_[ℓ]] (_root_.ConnectedComponents X → ℚ_[ℓ]) :=
  (PeriodInvariants.EtaleDegreeZero.sectionsEquivQp ℓ X).trans
    ((ConnectedComponentSections.equiv X ℚ_[ℓ] (Cohomology.Coeff.{u} ℓ)).trans
      (LinearEquiv.piCongrRight (fun _ =>
        (ULift.moduleEquiv : Cohomology.Coeff.{u} ℓ ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ]))))

theorem equiv_apply (z : Cohomology.RationalEllAdicCohomology ℓ X 0) (x : X) :
    equiv ℓ X z (ConnectedComponents.mk x) = (PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X z x).down := rfl

omit ℓ [Fact ℓ.Prime] in
def permutation (e : X ≅ X) : Equiv.Perm (_root_.ConnectedComponents X) :=
  ConnectedComponentSections.perm (Scheme.homeoOfIso e)

theorem pullback (e : X ≅ X) (z : Cohomology.RationalEllAdicCohomology ℓ X 0)
    (c : _root_.ConnectedComponents X) :
    equiv ℓ X (Frobenius.cohomologyPullback ℓ e 0 z) c = equiv ℓ X z (permutation X e c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change (PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X (Frobenius.cohomologyPullback ℓ e 0 z) x).down =
    (PeriodInvariants.EtaleDegreeZero.sectionsEquiv ℓ X z (e.hom x)).down
  exact congrArg ULift.down
    (congrArg (fun s => s x) (DegreeZeroPullback.pullback ℓ e z))

def endomorphism (e : X ≅ X) : Module.End ℚ_[ℓ] (Cohomology.RationalEllAdicCohomology ℓ X 0) :=
  (Frobenius.cohomologyPullback ℓ e 0).toLinearMap.restrictScalars ℚ_[ℓ]

theorem conjugate (e : X ≅ X) :
    (equiv ℓ X).conj (endomorphism ℓ X e) =
      PermutationPolynomial.Characteristic.action (permutation X e) ℚ_[ℓ] := by
  apply LinearMap.ext
  intro f
  funext c
  change equiv ℓ X (Frobenius.cohomologyPullback ℓ e 0 ((equiv ℓ X).symm f)) c = f (permutation X e c)
  rw [pullback, LinearEquiv.apply_symm_apply]

local instance : Fintype (_root_.ConnectedComponents X) := Fintype.ofFinite _
local instance : DecidableEq (_root_.ConnectedComponents X) := Classical.decEq _

theorem finrank : Module.finrank ℚ_[ℓ] (Cohomology.RationalEllAdicCohomology ℓ X 0) =
    Nat.card (_root_.ConnectedComponents X) := by
  rw [(equiv ℓ X).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

omit ℓ [Fact ℓ.Prime] in
def polynomial (e : X ≅ X) : Polynomial ℤ :=
  PermutationPolynomial.Characteristic.polynomial (permutation X e)

omit ℓ [Fact ℓ.Prime] in
theorem polynomial_monic (e : X ≅ X) : (polynomial X e).Monic :=
  PermutationPolynomial.Characteristic.monic _

theorem charpoly (e : X ≅ X) :
    (endomorphism ℓ X e).charpoly = (polynomial X e).map (Int.castRingHom ℚ_[ℓ]) := by
  rw [← (equiv ℓ X).charpoly_conj, conjugate,
    PermutationPolynomial.Characteristic.charpoly]
  rfl

theorem trace_pow (e : X ≅ X) (n : ℕ) :
    LinearMap.trace ℚ_[ℓ] (Cohomology.RationalEllAdicCohomology ℓ X 0) (endomorphism ℓ X e ^ n) =
      ((Finset.univ.filter (fun c => (permutation X e ^ n) c = c)).card : ℚ_[ℓ]) := by
  rw [← LinearMap.trace_conj' _ (equiv ℓ X)]
  have h : (equiv ℓ X).conj (endomorphism ℓ X e ^ n) =
      ((equiv ℓ X).conj (endomorphism ℓ X e)) ^ n :=
    ((equiv ℓ X).conjAlgEquiv ℚ_[ℓ]).map_pow _ n
  rw [h, conjugate, PermutationPolynomial.Characteristic.trace_pow]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConnectedComponents
