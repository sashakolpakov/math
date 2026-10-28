import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.NilLifting
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Coordinate Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateLifting

noncomputable section

/-!
# IntegralComparison: étale lifts with prescribed polynomial coordinates through nil ideals
-/

universe u

variable (R σ C G D : Type u) [CommRing R] [CommRing C] [CommRing G] [CommRing D]
  [Algebra R C] [Algebra (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) C]
  [Algebra R G] [Algebra R D]
  (π : G →ₐ[R] D) (hπ : Function.Surjective π)
  (hnil : ∀ b ∈ RingHom.ker π.toRingHom, IsNilpotent b)

local notation "P" => MvPolynomial σ R

include hπ hnil in
theorem exists_lift [Algebra.Etale (MvPolynomial σ R) C]
    (a : C →ₐ[R] D) (v : σ → G)
    (hv : ∀ i, π (v i) = a (algebraMap P C (MvPolynomial.X i))) :
    ∃ l : C →ₐ[R] G, π.comp l = a ∧ ∀ i, l (algebraMap P C (MvPolynomial.X i)) = v i := by
  let gP : P →ₐ[R] G := MvPolynomial.aeval v
  let dP : P →ₐ[R] D := a.comp (IsScalarTower.toAlgHom R P C)
  have hg : π.comp gP = dP := by
    apply MvPolynomial.algHom_ext
    intro i
    change π (MvPolynomial.aeval v (MvPolynomial.X i)) = a (algebraMap P C (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    exact hv i
  let : Algebra P G := gP.toRingHom.toAlgebra
  let : Algebra P D := dP.toRingHom.toAlgebra
  let : IsScalarTower R P G := IsScalarTower.of_algebraMap_eq' gP.comp_algebraMap.symm
  let q : G →ₐ[P] D := { π.toRingHom with commutes' := AlgHom.congr_fun hg }
  let aP : C →ₐ[P] D := { a.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨l, hl, _⟩ := NilLifting.existsUnique_lift aP q hπ hnil
  refine ⟨l.restrictScalars R, ?_, ?_⟩
  · apply AlgHom.ext
    intro c
    exact AlgHom.congr_fun hl c
  · intro i
    exact (l.commutes (MvPolynomial.X i)).trans (MvPolynomial.aeval_X v i)

include hnil in
theorem lift_unique [Algebra.FinitePresentation (MvPolynomial σ R) C]
    [Algebra.FormallyUnramified (MvPolynomial σ R) C]
    (l₁ l₂ : C →ₐ[R] G) (h : π.comp l₁ = π.comp l₂)
    (hv : ∀ i, l₁ (algebraMap P C (MvPolynomial.X i)) = l₂ (algebraMap P C (MvPolynomial.X i))) :
    l₁ = l₂ := by
  let gP : P →ₐ[R] G := l₁.comp (IsScalarTower.toAlgHom R P C)
  have hg : l₂.comp (IsScalarTower.toAlgHom R P C) = gP := by
    apply MvPolynomial.algHom_ext
    intro i
    exact (hv i).symm
  let : Algebra P G := gP.toRingHom.toAlgebra
  let : Algebra P D := (π.comp gP).toRingHom.toAlgebra
  let q : G →ₐ[P] D := { π.toRingHom with commutes' := fun _ => rfl }
  let a₁ : C →ₐ[P] G := { l₁.toRingHom with commutes' := fun _ => rfl }
  let a₂ : C →ₐ[P] G := { l₂.toRingHom with commutes' := AlgHom.congr_fun hg }
  have he : a₁ = a₂ := NilLifting.lift_unique q hnil a₁ a₂ (AlgHom.ext (fun c => AlgHom.congr_fun h c))
  exact AlgHom.ext (fun c => AlgHom.congr_fun he c)

include hπ hnil in
theorem existsUnique_lift [Algebra.Etale (MvPolynomial σ R) C]
    (a : C →ₐ[R] D) (v : σ → G)
    (hv : ∀ i, π (v i) = a (algebraMap P C (MvPolynomial.X i))) :
    ∃! l : C →ₐ[R] G, π.comp l = a ∧ ∀ i, l (algebraMap P C (MvPolynomial.X i)) = v i := by
  obtain ⟨l, hl, hv'⟩ := exists_lift R σ C G D π hπ hnil a v hv
  refine ⟨l, ⟨hl, hv'⟩, fun l' hl' => ?_⟩
  exact lift_unique R σ C G D π hnil l' l (hl'.1.trans hl.symm)
    (fun i => (hl'.2 i).trans (hv' i).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateLifting
