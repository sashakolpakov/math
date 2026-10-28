import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.StablePage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralFiltrationLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroSourceCone

/-! # Convergence Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConvergenceLength

noncomputable section

/-! The fixed filtration pieces of a bounded tensor complex account for
the length of its actual total homology. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.ComposableArrows

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralFiltrationLength

theorem point_zero (d : ℕ) : SpectralFiltrationLength.point (-1) (d + 1) 0 = ((-1 : ℤ) : EInt) := by
  simp [SpectralFiltrationLength.point]

theorem point_last (d : ℕ) : SpectralFiltrationLength.point (-1) (d + 1) (d + 1) = ((d : ℤ) : EInt) := by
  unfold SpectralFiltrationLength.point
  congr 1
  simp only [min_self, Nat.cast_add, Nat.cast_one]
  omega

theorem point_step (d i : ℕ) (hi : i ≤ d + 1) : SpectralFiltrationLength.point (-1) (d + 1) i = (((i : ℤ) - 1 : ℤ) : EInt) := by
  unfold SpectralFiltrationLength.point
  rw [Nat.min_eq_left hi]
  congr 1

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)

def gradedIso (d : ℕ) (n : ℤ) (i : ℕ) (hi : i < d + 1) :
    SpectralFiltrationLength.graded R (SpectralObject.abelian R K (BrutalFiltration.filtration R A))
      (-1) (d + 1) n i ≅
    StablePage.term R A K d ((i : ℤ) - 1) n (by omega) (by omega) := by
  let D := BrutalFiltration.filtration R A
  let X := SpectralObject.abelian R K D
  let f₁ := SpectralFiltrationLength.lower (-1) (d + 1) i
  let f₂ := SpectralFiltrationLength.step (-1) (d + 1) i
  let f₃ := SpectralFiltrationLength.upper (-1) (d + 1) (i + 1)
  let g₁ := StablePage.arrow (show -1 ≤ (i : ℤ) - 1 by omega)
  let g₂ := StablePage.arrow (show (i : ℤ) - 1 ≤ ((i : ℤ) - 1) + 1 by omega)
  let g₃ := StablePage.arrow (show ((i : ℤ) - 1) + 1 ≤ (d : ℤ) by omega)
  have hnext : SpectralFiltrationLength.point (-1) (d + 1) (i + 1) = ((((i : ℤ) - 1) + 1 : ℤ) : EInt) := by
    rw [point_step d (i + 1) (by omega)]
    congr 1
    omega
  let e : mk₃ f₁ f₂ f₃ ≅ mk₃ g₁ g₂ g₃ :=
    isoMk₃ (eqToIso (point_zero d)) (eqToIso (point_step d i (by omega)))
      (eqToIso hnext) (eqToIso (point_last d))
      (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let : IsIso (X.map f₁ f₂ f₃ g₁ g₂ g₃ e.hom (n - 1) n (n + 1)) :=
    SpectralIsomorphisms.E_map_isIso R K D _ _ _ _ _ _ e.hom (fun t => by infer_instance) n
  exact asIso (X.map f₁ f₂ f₃ g₁ g₂ g₃ e.hom (n - 1) n (n + 1) (sub_add_cancel _ _) rfl)

def endpointIso (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (n : ℤ) :
    ((SpectralObject.abelian R K (BrutalFiltration.filtration R A)).H n).obj
      (mk₁ (SpectralFiltrationLength.lower (-1) (d + 1) (d + 1))) ≅
    ((Homotopy.complexFunctor R K).obj A).homology n := by
  let D := BrutalFiltration.filtration R A
  let f := SpectralFiltrationLength.lower (-1) (d + 1) (d + 1)
  have hz : IsZero (D.obj (SpectralFiltrationLength.point (-1) (d + 1) 0)) := by
    change IsZero (BrutalFiltration.complex R A (SpectralFiltrationLength.point (-1) (d + 1) 0))
    rw [point_zero]
    exact BrutalFiltration.Bounds.stage_zero R A 0 (-1) hu (by omega)
  let : IsIso (BrutalFiltration.toComplex R A (SpectralFiltrationLength.point (-1) (d + 1) (d + 1))) := by
    rw [point_last]
    exact BrutalFiltration.Bounds.toComplex_isIso R A (-(d : ℤ)) (d : ℤ) hl (by omega)
  exact SpectralObject.termIso R K D f n ≪≫
    HomologicalComplex.homologyMapIso ((Homotopy.complexFunctor R K).mapIso
      ((ZeroSourceCone.iso R (D.map f) hz).symm ≪≫
        asIso (BrutalFiltration.toComplex R A (SpectralFiltrationLength.point (-1) (d + 1) (d + 1))))) n

theorem total_length_eq (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (n : ℤ) :
    Module.length R (((Homotopy.complexFunctor R K).obj A).homology n) =
      ∑ i ∈ Finset.range (d + 1), Module.length R
        (SpectralFiltrationLength.graded R (SpectralObject.abelian R K (BrutalFiltration.filtration R A))
          (-1) (d + 1) n i) := by
  rw [← (endpointIso R A K d hl hu n).toLinearEquiv.length_eq]
  exact SpectralFiltrationLength.length_eq_sum R _ (-1) (d + 1) n

def gradedPageIso (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (r : ℤ) (hr : (d : ℤ) + 3 ≤ r)
    (n : ℤ) (i : ℕ) (hi : i < d + 1) :
    SpectralFiltrationLength.graded R (SpectralObject.abelian R K (BrutalFiltration.filtration R A))
      (-1) (d + 1) n i ≅
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X
      (n - ((i : ℤ) - 1), (i : ℤ) - 1) := by
  refine gradedIso R A K d n i hi ≪≫ ?_
  convert (StablePage.iso R A K d hl hu r hr
    (n - ((i : ℤ) - 1)) ((i : ℤ) - 1) (by omega) (by omega)).symm using 2
  omega

theorem total_length_latePage (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (r : ℤ) (hr : (d : ℤ) + 3 ≤ r) (n : ℤ) :
    Module.length R (((Homotopy.complexFunctor R K).obj A).homology n) =
      ∑ i ∈ Finset.range (d + 1), Module.length R
        (((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X
          (n - ((i : ℤ) - 1), (i : ℤ) - 1)) := by
  rw [total_length_eq R A K d hl hu n]
  apply Finset.sum_congr rfl
  intro i hi
  exact (gradedPageIso R A K d hl hu r hr n i (Finset.mem_range.mp hi)).toLinearEquiv.length_eq

theorem total_rationalLength_latePage (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (r : ℤ) (hr : (d : ℤ) + 3 ≤ r) (n : ℤ)
    (hlen : ∀ i ∈ Finset.range (d + 1), Module.length R
      (((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X
        (n - ((i : ℤ) - 1), (i : ℤ) - 1)) ≠ ⊤) :
    ExactLength.rationalLength R (((Homotopy.complexFunctor R K).obj A).homology n) =
      ∑ i ∈ Finset.range (d + 1), ExactLength.rationalLength R
        (((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X
          (n - ((i : ℤ) - 1), (i : ℤ) - 1)) := by
  simp only [ExactLength.rationalLength]
  rw [total_length_latePage R A K d hl hu r hr n, ENat.toNat_sum hlen, Nat.cast_sum]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConvergenceLength
