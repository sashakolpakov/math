import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FixedRankCokernel
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Cokernel Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization

noncomputable section

/-! Flatness and prescribed rank of a finite matrix cokernel are detected by its actual localized matrices. -/

open TensorProduct OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FixedRankCokernel.Grassmannian

universe u

variable {R : Type u} [CommRing R] {μ ν : Type u}
variable [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
variable (A : Matrix ν μ R)

def matrixCokernelBaseChangeEquiv (S : Type u) [CommRing S] [Algebra R S] :
    ((ν → S) ⧸ (Matrix.toLin' (A.map (algebraMap R S))).range) ≃ₗ[S]
      S ⊗[R] ((ν → R) ⧸ (Matrix.toLin' A).range) :=
  (Submodule.quotEquivOfEq _ _ (SurjectivityBaseChange.coordinateSubmoduleExtension_matrixRange (algebraMap R S) A).symm).trans
    (HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateBaseChangeQuotientEquiv (S := S) (Matrix.toLin' A).range)

theorem matrixCokernel_rankAtStalk (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' A).range) p =
      Module.finrank (Localization.AtPrime p.asIdeal)
        ((ν → Localization.AtPrime p.asIdeal) ⧸
          (Matrix.toLin' (A.map (algebraMap R (Localization.AtPrime p.asIdeal)))).range) :=
  (Module.rankAtStalk_eq_finrank_tensorProduct p).trans
    (matrixCokernelBaseChangeEquiv A (Localization.AtPrime p.asIdeal)).finrank_eq.symm

theorem matrixCokernel_flat_iff_localizations :
    Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) ↔
      ∀ p : PrimeSpectrum R, Module.Flat (Localization.AtPrime p.asIdeal)
        ((ν → Localization.AtPrime p.asIdeal) ⧸
          (Matrix.toLin' (A.map (algebraMap R (Localization.AtPrime p.asIdeal)))).range) := by
  constructor
  · intro h p
    let := h
    exact Module.Flat.of_linearEquiv (matrixCokernelBaseChangeEquiv A (Localization.AtPrime p.asIdeal))
  · intro h
    apply Module.flat_of_localized_maximal
    intro P hP
    let S := Localization.AtPrime P
    let M := (ν → R) ⧸ (Matrix.toLin' A).range
    let := h ⟨P, inferInstance⟩
    let : Module.Flat S (S ⊗[R] M) :=
      Module.Flat.of_linearEquiv (matrixCokernelBaseChangeEquiv A S).symm
    rw [← Module.flat_iff_of_isLocalization S P.primeCompl]
    exact Module.Flat.of_linearEquiv (LocalizedModule.equivTensorProduct P.primeCompl M)

theorem matrixCokernel_flatRank_iff_localizations (q : ℕ) :
    (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) ∧
      ∀ p, Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' A).range) p + q = Fintype.card ν) ↔
    ∀ p : PrimeSpectrum R,
      Module.Flat (Localization.AtPrime p.asIdeal)
        ((ν → Localization.AtPrime p.asIdeal) ⧸
          (Matrix.toLin' (A.map (algebraMap R (Localization.AtPrime p.asIdeal)))).range) ∧
      Module.finrank (Localization.AtPrime p.asIdeal)
        ((ν → Localization.AtPrime p.asIdeal) ⧸
          (Matrix.toLin' (A.map (algebraMap R (Localization.AtPrime p.asIdeal)))).range) + q = Fintype.card ν := by
  rw [matrixCokernel_flat_iff_localizations]
  simp only [matrixCokernel_rankAtStalk A]
  exact forall_and.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization
