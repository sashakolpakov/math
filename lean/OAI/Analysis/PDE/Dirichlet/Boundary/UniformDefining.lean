import OAI.Analysis.PDE.Dirichlet.Coercivity
import OAI.Analysis.PDE.Dirichlet.Boundary.Coercivity
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

noncomputable section
open Set Module
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise RealInnerProductSpace
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem gradientMap_fourSlots_surjective {n : ℕ} :
    Function.Surjective (fun v : CoordinateSpace n 4 => OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v) := by
  intro z
  refine ⟨WithLp.toLp 2 (fun i : Fin n × Fin 4 =>
    ![(z i.1).re, (z i.1).imI, (z i.1).imJ, (z i.1).imK] i.2), ?_⟩
  funext i
  dsimp only
  rw [OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots]
  ext <;> rfl

theorem quaternionForm_one_gradient {n : ℕ} (v : CoordinateSpace n 4) :
    (quaternionForm (1 : Matrix (Fin n) (Fin n) Q) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v)).re =
      ‖v‖ ^ 2 := by
  rw [OAI.LinearAlgebra.Moore.quaternionForm_eq_dotProduct, Matrix.one_mulVec]
  change (quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v)).re = _
  rw [quaternionPairing_gradient_re, real_inner_self_eq_norm_sq]

/-- Pointwise strict quaternionic positivity on a compact set yields a
uniform positive scalar shift, without a supplied ellipticity constant. -/
theorem compact_positive_quaternion_shift
    {X : Type*} [TopologicalSpace X] {n : ℕ} (hn : 1 ≤ n)
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (A : X → Matrix (Fin n) (Fin n) Q) (hA : Continuous A)
    (hpos : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K,
      (OAI.LinearAlgebra.Moore.complexify (A x - c • (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef := by
  obtain ⟨c,hc,hlower⟩ := inversePrincipalSymbol_uniform_bound hn hK hne A hA hpos
  refine ⟨c,hc,fun x hx => ?_⟩
  have hH : (A x - c • (1 : Matrix (Fin n) (Fin n) Q)).IsHermitian :=
    (OAI.LinearAlgebra.Moore.isHermitian_of_complexify (hpos x hx).isHermitian).sub
      (by
        change (c • (1 : Matrix (Fin n) (Fin n) Q))ᴴ = c • 1
        rw [OAI.LinearAlgebra.Moore.quaternionMatrix_conjTranspose_real_smul, Matrix.conjTranspose_one])
  apply (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff hH).mpr
  intro z
  obtain ⟨v,rfl⟩ := gradientMap_fourSlots_surjective z
  have h := hlower x hx v
  rw [quaternionForm_sub, quaternionForm_smul_matrix]
  change 0 ≤ (quaternionForm (A x) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v)).re -
    c * (quaternionForm (1 : Matrix (Fin n) (Fin n) Q) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v)).re
  rw [quaternionForm_one_gradient]
  exact sub_nonneg.mpr h

/-- The defining-function ellipticity constant follows from the original
pointwise positivity hypothesis and compactness modulo the spatial lattice. -/
theorem uniform_defining_hessian_shift
    {n : ℕ} (hn : 1 ≤ n) {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x -
        c • (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef := by
  have hcell : (latticeSublevelCell e lat K r).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨latticeRepresentative e lat x,
      latticeRepresentative_mem_sublevelCell e lat hrp hbounded hx⟩
  obtain ⟨c,hc,hshift⟩ := compact_positive_quaternion_shift hn
    (isCompact_latticeSublevelCell e lat hK hr.continuous) hcell
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r) (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hr)
    (fun x hx => hpos x hx.2)
  refine ⟨c,hc,fun x hx => ?_⟩
  have hy := latticeRepresentative_mem_sublevelCell e lat hrp hbounded hx
  have h := hshift (latticeRepresentative e lat x) hy
  rwa [(hrp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).representative x] at h

end OAI.Analysis.PDE.Dirichlet
