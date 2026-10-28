import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale

/-! # Projective Point Injective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointInjective

noncomputable section

/-!
# Homogeneous coordinates separate actual projective scheme points

If two nonzero coordinate vectors define the same underlying `Proj` point,
homogeneous linear equations show that the vectors are nonzero scalar multiples.
Consequently the previously constructed map from ordinary projectivization to
actual complex-valued projective scheme points is injective.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {n : ℕ}

/-- Equality of the actual underlying projective scheme points forces two
nonzero homogeneous coordinate vectors to differ by a nonzero scalar. -/
theorem exists_smul_eq_of_projectiveVectorPoint_apply_eq
    (v w : Fin (n + 1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) (x : ProjectiveSpace.complexBase)
    (heq : ProjectiveVectorPoint.projectiveVectorPoint v hv x = ProjectiveVectorPoint.projectiveVectorPoint w hw x) :
    ∃ c : ℂ, c ≠ 0 ∧ w = c • v := by
  classical
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hvi⟩ := hex
  have hwi : w i ≠ 0 := by
    apply (ProjectiveVectorPoint.projectiveVectorPoint_mem_coordinateOpen_iff w hw i x).mp
    rw [← heq]
    exact (ProjectiveVectorPoint.projectiveVectorPoint_mem_coordinateOpen_iff v hv i x).mpr hvi
  refine ⟨w i / v i, div_ne_zero hwi hvi, ?_⟩
  funext j
  let f : ProjectiveSpace.homogeneousCoordinateRing n :=
    MvPolynomial.C (v i) * MvPolynomial.X j -
      MvPolynomial.C (v j) * MvPolynomial.X i
  have hf : f ∈ ProjectiveSpace.projectiveGrading n 1 :=
    (MvPolynomial.isHomogeneous_C_mul_X (v i) j).sub
      (MvPolynomial.isHomogeneous_C_mul_X (v j) i)
  have hvf : MvPolynomial.eval v f = 0 := by
    simp [f, mul_comm]
  have hmem : f ∈ (ProjectiveVectorPoint.projectiveVectorPoint v hv x).asHomogeneousIdeal :=
    (ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff v hv f 1 hf x).mpr hvf
  rw [heq] at hmem
  have hwf : MvPolynomial.eval w f = 0 :=
    (ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff w hw f 1 hf x).mp hmem
  have hcross : v i * w j = v j * w i := by
    apply sub_eq_zero.mp
    simpa [f] using hwf
  change w j = (w i / v i) * v j
  calc
    w j = (v j * w i) / v i :=
      (eq_div_iff hvi).mpr (by simpa [mul_comm] using hcross)
    _ = (w i / v i) * v j := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Equal underlying scheme points give equal points of mathlib's ordinary
projectivization. -/
theorem projectivization_mk_eq_of_projectiveVectorPoint_apply_eq
    (v w : Fin (n + 1) → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) (x : ProjectiveSpace.complexBase)
    (heq : ProjectiveVectorPoint.projectiveVectorPoint v hv x = ProjectiveVectorPoint.projectiveVectorPoint w hw x) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  obtain ⟨c, _, hcv⟩ :=
    exists_smul_eq_of_projectiveVectorPoint_apply_eq v w hv hw x heq
  exact ((Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mpr ⟨c, hcv.symm⟩).symm

/-- Even forgetting the scheme morphism and remembering only its underlying
point gives an injective map from ordinary projective space. -/
theorem projectivizationPoint_apply_injective (n : ℕ) (x : ProjectiveSpace.complexBase) :
    Function.Injective
      (fun p : Projectivization ℂ (Fin (n + 1) → ℂ) => ProjectiveVectorScale.projectivizationPoint n p x) := by
  intro p q heq
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      exact projectivization_mk_eq_of_projectiveVectorPoint_apply_eq v w hv hw x heq

/-- The constructed map from ordinary projectivization to actual
complex-valued projective scheme points is injective. -/
theorem projectivizationPoint_injective (n : ℕ) :
    Function.Injective (ProjectiveVectorScale.projectivizationPoint n) := by
  intro p q heq
  apply projectivizationPoint_apply_injective n (default : ProjectiveSpace.complexBase)
  exact congrArg (fun f : ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n => f (default : ProjectiveSpace.complexBase)) heq

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointInjective
