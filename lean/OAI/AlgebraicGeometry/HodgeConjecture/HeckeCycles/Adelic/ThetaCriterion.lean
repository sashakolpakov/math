import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Theta Criterion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaCriterion.CM

noncomputable section

/-! The actual AdelicTheta Hodge subspace is characterized by its line,
annihilator, and selected compact components. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K)

def Criterion (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) : Prop :=
  ∀ v j, if v = A.distinguished then
    (∃ c : ℂ, ∀ i, (w v).1 (i, j) = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val i * c) ∧
      dotProduct (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val) (fun i => (w v).2 (i, j)) = 0
    else if A.positive v j then (∀ i, (w v).2 (i, j) = 0)
    else (∀ i, (w v).1 (i, j) = 0)

theorem distinguished (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) (h : Criterion A z w) (j : Fin m) :
    (∃ c : ℂ, ∀ i, (w A.distinguished).1 (i, j) = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val i * c) ∧
      dotProduct (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val) (fun i => (w A.distinguished).2 (i, j)) = 0 := by
  have hj := h A.distinguished j
  rwa [ite_eq_left rfl] at hj

theorem compact (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) (h : Criterion A z w)
    (v : Fin A.places) (hv : v ≠ A.distinguished) (j : Fin m) :
    if A.positive v j then (∀ i, (w v).2 (i, j) = 0) else (∀ i, (w v).1 (i, j) = 0) := by
  have hj := h v j
  rwa [ite_eq_right hv] at hj

theorem of_components (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A)
    (hd : ∀ j : Fin m,
      (∃ c : ℂ, ∀ i, (w A.distinguished).1 (i, j) = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val i * c) ∧
        dotProduct (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val) (fun i => (w A.distinguished).2 (i, j)) = 0)
    (hc : ∀ v : Fin A.places, v ≠ A.distinguished → ∀ j : Fin m,
      if A.positive v j then (∀ i, (w v).2 (i, j) = 0) else (∀ i, (w v).1 (i, j) = 0)) :
    Criterion A z w := by
  intro v j
  by_cases hv : v = A.distinguished
  · subst v
    rw [ite_eq_left rfl]
    exact hd j
  · rw [ite_eq_right hv]
    exact hc v hv j

theorem frame_criterion (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (a : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) : Criterion A z (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z a) := by
  intro v j
  by_cases hv : v = A.distinguished
  · rw [ite_eq_left hv]
    constructor
    · exact ⟨a (v, 0, j), fun i => by simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_left hv]⟩
    · simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, hv, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector, dotProduct, Fin.sum_univ_succ]
  · rw [ite_eq_right hv]
    by_cases hp : A.positive v j
    · rw [ite_eq_left hp]
      intro i
      simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_right hv, ite_eq_left hp]
    · rw [ite_eq_right hp]
      intro i
      simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_right hv, ite_eq_right hp]

theorem reconstruct (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) (hw : Criterion A z w) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates A w) = w := by
  funext v
  apply Prod.ext
  · funext ij
    have h := hw v ij.2
    by_cases hv : v = A.distinguished
    · rw [ite_eq_left hv] at h
      obtain ⟨c, hc⟩ := h.1
      have hc2 : (w v).1 (2, ij.2) = c := by simpa [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector] using hc 2
      simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, ite_eq_left hv, ite_true]
      rw [hc2]
      exact (hc ij.1).symm
    · rw [ite_eq_right hv] at h
      by_cases hp : A.positive v ij.2
      · simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, ite_eq_right hv, ite_eq_left hp]
      · rw [ite_eq_right hp] at h
        simpa only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_right hv, ite_eq_right hp] using (h ij.1).symm
  · funext ij
    have h := hw v ij.2
    by_cases hv : v = A.distinguished
    · rw [ite_eq_left hv] at h
      have hf := RepresentationTheory.Theta.Adelic.AnnihilatorFrame.annihilator_frame_coordinates z.val (fun i => (w v).2 (i, ij.2)) h.2
      have hi := congrFun hf ij.1
      rcases ij with ⟨i, j⟩
      fin_cases i
      · simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, hv, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector]
      · simp [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, hv, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector]
      · simpa [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, hv, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector, RepresentationTheory.Theta.Adelic.AnnihilatorFrame.frameVector, add_comm] using hi.symm
    · rw [ite_eq_right hv] at h
      by_cases hp : A.positive v ij.2
      · rw [ite_eq_left hp] at h
        simpa only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, ite_eq_right hv, ite_eq_left hp] using (h ij.1).symm
      · simp only [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame, RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, ite_eq_right hv, ite_eq_right hp]

theorem mem_iff (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (w : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A) : w ∈ RepresentationTheory.Theta.Adelic.BallGeometryData.HodgeSubspace A z ↔ Criterion A z w := by
  constructor
  · rintro ⟨a, rfl⟩
    exact frame_criterion A z a
  · intro hw
    exact ⟨RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates A w, reconstruct A z w hw⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaCriterion.CM
