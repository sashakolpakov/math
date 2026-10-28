import OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Two Stage Presentation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation

noncomputable section

open _root_.MvPolynomial

/-! Finite two-stage presentations by negative twists with ordered generator degrees. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwistCoproduct_quasicoherent (j : σ) {r : ℕ} (d : Fin r → ℕ) :
    (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)).IsQuasicoherent := by
  apply Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct
  intro k
  exact InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (R := R) j (d k))

theorem negativeTwistCoproduct_finiteType (j : σ) {r : ℕ} (d : Fin r → ℕ) :
    (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)).IsFiniteType := by
  apply Quasicoherent.Scheme.Modules.isFiniteType_fin_coproduct
  · intro k
    exact InvertibleFinitePresentation.invertible_quasicoherent
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (R := R) j (d k))
  · intro k
    have : (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)).IsFinitePresentation :=
      InvertibleFinitePresentation.invertible_finitePresentation
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (R := R) j (d k))
    infer_instance

structure CoordinateNegativeTwistPresentation (j : σ)
    (M : (Proj (homogeneousSubmodule σ R)).Modules) where
  rows : ℕ
  columns : ℕ
  rowDegree : Fin rows → ℕ
  columnDegree : Fin columns → ℕ
  projection : (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (rowDegree k)) ⟶ M
  relations : (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (columnDegree k)) ⟶
    (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (rowDegree k))
  epi : Epi projection
  zero : relations ≫ projection = 0
  exact : (ShortComplex.mk relations projection zero).Exact
  degree_order : ∀ k l, rowDegree k ≤ columnDegree l

theorem exists_coordinateNegativeTwistPresentation [Fintype σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) : Nonempty (CoordinateNegativeTwistPresentation j M) := by
  classical
  obtain ⟨r, d, f, hf⟩ := FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient M j
  let Q := ∐ fun k : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)
  have : Q.IsQuasicoherent := negativeTwistCoproduct_quasicoherent j d
  have : Q.IsFiniteType := negativeTwistCoproduct_finiteType j d
  have : LocallyOfFiniteType (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  have : (kernel f).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  have : (kernel f).IsFiniteType := Quasicoherent.Scheme.Modules.isFiniteType_kernel f
  let B := Finset.univ.sup d
  obtain ⟨s, e, p, he, hp⟩ := BoundedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient_above (kernel f) j B
  have : Epi p := hp
  let g := p ≫ kernel.ι f
  have hg : g ≫ f = 0 := by simp [g]
  have hex : (ShortComplex.mk g f hg).Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have heq : kernel.lift f g hg = p := by
      apply (cancel_mono (kernel.ι f)).mp
      simp [g]
    rw [heq]
    infer_instance
  exact ⟨{ rows := r
           columns := s
           rowDegree := d
           columnDegree := e
           projection := f
           relations := g
           epi := hf
           zero := hg
           exact := hex
           degree_order := fun k l => (Finset.le_sup (f := d) (Finset.mem_univ k)).trans (he l) }⟩

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation
