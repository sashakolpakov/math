import OAI.Analysis.PDE.Variational.WeakGradient
import OAI.Analysis.PDE.Dirichlet.VariationalEnergy

open Set _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

section Hilbert
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem isCoercive_flip (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) :
    IsCoercive B.flip := by
  obtain ⟨C, hC, h⟩ := hB
  exact ⟨C, hC, h⟩

/-- The actual Lax–Milgram solution, obtained from the coercive form and the Riesz
representative of its right-hand side. No inverse operator is assumed. -/
def laxMilgramSolution (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (l : V →L[ℝ] ℝ) : V :=
  hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm l)

theorem laxMilgramSolution_eq (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (l : V →L[ℝ] ℝ) (v : V) : B (laxMilgramSolution B hB l) v = l v := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp [laxMilgramSolution, InnerProductSpace.toDual_symm_apply]

theorem laxMilgramSolution_unique (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (l : V →L[ℝ] ℝ) {u : V} (hu : ∀ v, B u v = l v) :
    u = laxMilgramSolution B hB l := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply,
    hB.continuousLinearEquivOfBilin_apply, hu, laxMilgramSolution_eq]

theorem exists_unique_bilinear_solution (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (l : V →L[ℝ] ℝ) : ∃! u, ∀ v, B u v = l v :=
  ⟨laxMilgramSolution B hB l, laxMilgramSolution_eq B hB l,
    fun _ h ↦ laxMilgramSolution_unique B hB l h⟩

end Hilbert

variable {m : ℕ}

def periodicEnergy (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (B : Lp (CellVectors m) 2 (volume.restrict (Icc a b)) →L[ℝ]
      Lp (CellVectors m) 2 (volume.restrict (Icc a b)) →L[ℝ] ℝ) :
    PeriodicH10 a b Ω P →L[ℝ] PeriodicH10 a b Ω P →L[ℝ] ℝ :=
  B.bilinearComp (testGradientMap a b Ω P).range.topologicalClosure.subtypeL
    (testGradientMap a b Ω P).range.topologicalClosure.subtypeL

theorem periodicEnergy_isCoercive (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (B : Lp (CellVectors m) 2 (volume.restrict (Icc a b)) →L[ℝ]
      Lp (CellVectors m) 2 (volume.restrict (Icc a b)) →L[ℝ] ℝ)
    (hB : IsCoercive B) : IsCoercive (periodicEnergy a b Ω P B) := by
  obtain ⟨C, hC, h⟩ := hB
  exact ⟨C, hC, fun u ↦ h u.val⟩

def periodicLoad (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) : PeriodicH10 a b Ω P →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (periodicValue a b Ω P)

theorem periodicLoad_eq_integral (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) (v : PeriodicH10 a b Ω P) :
    periodicLoad a b Ω P f v = ∫ x in Icc a b, f x * periodicValue a b Ω P v x := by
  change inner ℝ f (periodicValue a b Ω P v) = _
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

theorem periodicEnergy_coefficient (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖ ≤ M)
    (u v : PeriodicH10 a b Ω P) :
    periodicEnergy a b Ω P (OAI.Analysis.PDE.Dirichlet.coefficientEnergy A hA hM hAM).flip u v =
      ∫ x in Icc a b, inner ℝ (v.val x) (A x (u.val x)) :=
  OAI.Analysis.PDE.Dirichlet.coefficientEnergy_eq_integral A hA hM hAM v.val u.val

/-- Existence and uniqueness in the concrete closed test-gradient space for every
bounded measurable uniformly elliptic coefficient field and every L² load. -/
theorem exists_unique_periodic_weak_solution (a b : CellCoordinates m)
    (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M lam : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖ ≤ M) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ v : CellVectors m,
      lam * ‖v‖^2 ≤ inner ℝ v (A x v))
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ∃! u : PeriodicH10 a b Ω P, ∀ v : PeriodicH10 a b Ω P,
      (∫ x in Icc a b, inner ℝ (v.val x) (A x (u.val x))) =
        ∫ x in Icc a b, f x * periodicValue a b Ω P v x := by
  let B := (OAI.Analysis.PDE.Dirichlet.coefficientEnergy A hA hM hAM).flip
  have hB : IsCoercive B := isCoercive_flip _
    (OAI.Analysis.PDE.Dirichlet.coefficientEnergy_isCoercive A hA hM hAM hlam hell)
  have h := exists_unique_bilinear_solution (periodicEnergy a b Ω P B)
    (periodicEnergy_isCoercive a b Ω P B hB) (periodicLoad a b Ω P f)
  simpa only [B, periodicEnergy_coefficient, periodicLoad_eq_integral] using h

end OAI.Analysis.PDE.Variational
