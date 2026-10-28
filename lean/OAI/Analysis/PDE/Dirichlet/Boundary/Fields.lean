import OAI.Analysis.PDE.Dirichlet.FamilyForcing

open Set Filter Metric
open scoped Topology Matrix ComplexOrder MatrixOrder InnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

def boundaryRotation {n : ℕ} (r : CoordinateSpace n 4 → ℝ)
    (x e : CoordinateSpace n 4) : Matrix (Fin n) (Fin n) Q :=
  adaptedRotation (fderiv ℝ r x) (fderiv ℝ (fderiv ℝ r) x) e

def boundaryFieldLinear {n : ℕ} (r : CoordinateSpace n 4 → ℝ)
    (x e : CoordinateSpace n 4) : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 :=
  realMatrixAction (realRepresentation (boundaryRotation r x e))

def boundaryFieldTranslation {n : ℕ} (r : CoordinateSpace n 4 → ℝ)
    (x e : CoordinateSpace n 4) : CoordinateSpace n 4 :=
  e - boundaryFieldLinear r x e x

def boundaryFieldFactor {n : ℕ} (r : CoordinateSpace n 4 → ℝ)
    (x e : CoordinateSpace n 4) : ℝ :=
  fderiv ℝ (fderiv ℝ r) x (covectorNormal (fderiv ℝ r x)) e / ‖fderiv ℝ r x‖

theorem boundaryField_first_jet {n : ℕ} {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) {x : CoordinateSpace n 4} (hg : fderiv ℝ r x ≠ 0)
    (e : CoordinateSpace n 4) :
    fderiv ℝ (affineDerivative r (boundaryFieldTranslation r x e) (boundaryFieldLinear r x e)) x =
      boundaryFieldFactor r x e • fderiv ℝ r x := by
  let g := fderiv ℝ r x
  let H := fderiv ℝ (fderiv ℝ r) x
  let A := boundaryFieldLinear r x e
  let f := affineDerivative r (boundaryFieldTranslation r x e) A
  have hd (w) : fderiv ℝ f x w = g (A w) + H w e := by
    simpa only [f, A, boundaryFieldTranslation, directionalDerivative, sub_add_cancel] using
      directionalDerivative_affineDerivative hr (boundaryFieldTranslation r x e) A w x
  have hj := adaptedRotation_jet hg H e
  have hker : ∀ w, g w = 0 → fderiv ℝ f x w = 0 := by
    intro w hw
    rw [hd]
    exact hj.2 w hw
  obtain ⟨a, ha⟩ := linear_form_factor_of_kernel (fderiv ℝ f x) g hg hker
  have hv : g (covectorNormal g) = ‖g‖ := by
    have hv' := congrArg (fun l : CoordinateSpace n 4 →L[ℝ] ℝ ↦ l (covectorNormal g))
      (covectorNormal_form (g := g) hg)
    simpa [innerSL_apply_apply, covectorNormal_unit (g := g) hg] using hv'
  have heval := congrArg (fun l : CoordinateSpace n 4 →L[ℝ] ℝ ↦ l (covectorNormal g)) ha
  rw [hd] at heval
  change g (A (covectorNormal g)) + H (covectorNormal g) e = a * g (covectorNormal g) at heval
  have hnormal : g (A (covectorNormal g)) = 0 := hj.1
  rw [hnormal, zero_add, hv] at heval
  have haeq : a = boundaryFieldFactor r x e :=
    (eq_div_iff (norm_ne_zero_iff.mpr hg)).mpr heval.symm
  exact ha.trans (by rw [haeq])

/-- A single trace-weighted forcing bound works for every boundary center,
every unit tangent direction, and every unknown solution. -/
theorem exists_uniform_boundary_field_forcing {n : ℕ}
    {r B₀ F : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 2 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    {S K : Set (CoordinateSpace n 4)} (hS : IsCompact S) (hK : IsCompact K)
    (hreg : ∀ x ∈ S, fderiv ℝ r x ≠ 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, ∀ e : CoordinateSpace n 4, ‖e‖ ≤ 1 →
      ∀ u, ContDiff ℝ 3 u → ∀ y ∈ K,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y)).PosDef →
      κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y) 1 →
      (fun z ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun w ↦ B₀ w + u w) z)) =ᶠ[𝓝 y] F →
      |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z))
        (affineDerivative u (boundaryFieldTranslation r x e) (boundaryFieldLinear r x e)) y| ≤
        C * OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y) 1 := by
  let P := S × closedBall (0 : CoordinateSpace n 4) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace (closedBall (0 : CoordinateSpace n 4) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let z : P → CoordinateSpace n 4 := fun p ↦ p.1.1
  let e₀ : P → CoordinateSpace n 4 := fun p ↦ p.2.1
  have hz : Continuous z := continuous_subtype_val.comp continuous_fst
  have he : Continuous e₀ := continuous_subtype_val.comp continuous_snd
  let R : P → Matrix (Fin n) (Fin n) Q := fun p ↦ boundaryRotation r (z p) (e₀ p)
  have hR : Continuous R := continuous_boundaryRotation hr hz he (fun p ↦ hreg _ p.1.2)
  have hskew : ∀ p, (R p)ᴴ = -R p := fun p ↦
    (adaptedRotation_spec (hreg _ p.1.2) _ _).1
  have hA : Continuous (fun p : P ↦ boundaryFieldLinear r (z p) (e₀ p)) :=
    continuous_realMatrixAction.comp (continuous_realRepresentation hR)
  have htrans : Continuous (fun p : P ↦ boundaryFieldTranslation r (z p) (e₀ p)) :=
    he.sub (hA.clm_apply hz)
  obtain ⟨C, hC, hbound⟩ := exists_compact_family_rigid_forcing hB₀ hF htrans hR hskew hK hκ
  refine ⟨C, hC, ?_⟩
  intro x hx e he₁ u hu y hy hpos htrace heq
  have he' : e ∈ closedBall (0 : CoordinateSpace n 4) 1 := by simpa using he₁
  exact hbound (⟨x, hx⟩, ⟨e, he'⟩) u hu y hy hpos htrace heq

end OAI.Analysis.PDE.Dirichlet
