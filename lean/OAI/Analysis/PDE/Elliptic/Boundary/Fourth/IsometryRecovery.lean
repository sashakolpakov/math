import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.OperatorRecovery
import OAI.Analysis.PDE.Schauder.Boundary.FourthCoordinateSource
import OAI.Analysis.PDE.Schauder.Calculus.FourthHolderTransport

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Isometric conjugation preserves the actual coefficient Hölder norm. -/
theorem exists_operator_holder_isometry (e : E ≃ₗᵢ[ℝ] F)
    {S : Set F} {α : ℝ} (hα : 0 ≤ α) (a : F → F →L[ℝ] F)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap S (F →L[ℝ] F) α)
    (hA : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a x) :
    ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' S) (E →L[ℝ] E) α, ‖B‖ ≤ ‖A‖ ∧
      ∀ x : e ⁻¹' S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.PDE.Dirichlet.isometryConjugate e (a (e x)) := by
  let ι : (e ⁻¹' S) → S := fun x => ⟨e x,x.property⟩
  have hι : Continuous ι := by fun_prop
  let f : (e ⁻¹' S) → E →L[ℝ] E := fun x => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.Normed.Function.Holder.HolderMap.value A (ι x))
  have hf : Continuous f :=
    continuous_const.clm_comp (((OAI.Analysis.Normed.Function.Holder.HolderMap.value A).continuous.comp hι).clm_comp continuous_const)
  have hn (x : e ⁻¹' S) : ‖f x‖ ≤ ‖A‖ := by
    change ‖OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.Normed.Function.Holder.HolderMap.value A (ι x))‖ ≤ _
    rw [OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate]
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le A _
  have hh (x y : e ⁻¹' S) : ‖f x-f y‖ ≤ ‖A‖*dist x y^α := by
    change ‖OAI.Analysis.PDE.Dirichlet.isometryConjugate e _-OAI.Analysis.PDE.Dirichlet.isometryConjugate e _‖ ≤ _
    rw [← OAI.Analysis.PDE.Dirichlet.isometryConjugate_sub,OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate]
    simpa only [ι,Subtype.dist_eq,e.isometry.dist_eq] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le A (ι x) (ι y)
  let v := BoundedContinuousFunction.ofNormedAddCommGroup f hf ‖A‖ hn
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hh,?_,?_⟩
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα v (norm_nonneg A) hh).trans
    exact max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hf (norm_nonneg A) hn) le_rfl
  · intro x
    change OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.Normed.Function.Holder.HolderMap.value A (ι x)) = _
    rw [hA]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem exists_double_second_holder_isometry (e : E ≃ₗᵢ[ℝ] F)
    (u : F → ℝ) (hu : ContDiff ℝ 4 u) (v w : E) {S : Set F} {α : ℝ}
    (hα : 0 ≤ α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap S (F →L[ℝ] F →L[ℝ] ℝ) α)
    (hB : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e v)) (e w))) x) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' S) (E →L[ℝ] E →L[ℝ] ℝ) α, ‖H‖ ≤ ‖B‖ ∧
      ∀ x : e ⁻¹' S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x =
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) v) w)) x := by
  have hq : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e v)) (e w)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative
      (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 3) (by norm_num) _) (by norm_num) _
  obtain ⟨H,hH,hHn⟩ := OAI.Analysis.PDE.Schauder.exists_second_holder_isometry e _ hq hα B hB
  refine ⟨H,hHn,?_⟩
  intro x
  rw [OAI.Analysis.PDE.Schauder.double_directional_isometry_comp e u (hu.of_le (by norm_num))]
  exact hH x

variable {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)

/-- Normal fourth-order recovery is intrinsic: any orthonormal coordinate
frame in the physical space has the same estimate as the Euclidean frame. -/
theorem exists_uniform_fourth_holder_in_frame
    (e : X ≃ₗᵢ[ℝ] E) {α μ N : ℝ} (hα : 0 ≤ α) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set E) (u : E → ℝ), ContDiff ℝ 4 u → ∀ k : Fin m,
      ∀ (a : E → E →L[ℝ] E) (A : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
        (R : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (B : Fin m × Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a x) → ‖A‖ ≤ N →
      (∀ x : S, (a x).toLinearMap.IsSymmetric) →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B (i,j)) x =
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative
          (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e (EuclideanSpace.single i 1)))
          (e (EuclideanSpace.single j 1)))) x) →
      ∀ M Q, 0 ≤ M → 0 ≤ Q →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ‖B (i,j)‖ ≤ M) → (∀ i, ‖R i‖ ≤ Q) →
      (∀ x : S, μ ≤ inner ℝ (a x (e (EuclideanSpace.single k 1)))
        (e (EuclideanSpace.single k 1))) →
      (∀ i (x : S), ellipticTrace a
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (e (EuclideanSpace.single i 1)))
          (e (EuclideanSpace.single k 1))) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i) x) →
      HasFourthHolderBound S α u (C*(M+Q)) := by
  classical
  obtain ⟨C,hC,hrecover⟩ := exists_uniform_fourth_holder_of_operator (m := m) hα hμ hN
  refine ⟨C,hC,?_⟩
  intro S u hu k a A R B hA hAn hsym hB M Q hM hQ hBn hRn hpos heq
  obtain ⟨A',hA'n,hA'⟩ := exists_operator_holder_isometry e hα a A hA
  have hRex (i : Fin m) := OAI.Analysis.PDE.Schauder.exists_double_equation_isometry e a u hu hα
    (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) (R i) (heq i)
  choose R' hR'n hR' using hRex
  have hBex (p : Fin m × Fin m) :
      ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' S) (X →L[ℝ] X →L[ℝ] ℝ) α, ‖H‖ ≤ M ∧
        (p.1 ≠ k → p.2 ≠ k → ∀ x : e ⁻¹' S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x =
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative
            (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ e) (EuclideanSpace.single p.1 1))
            (EuclideanSpace.single p.2 1))) x) := by
    by_cases hi : p.1 = k
    · exact ⟨0,by simpa only [norm_zero] using hM,fun hn => (hn hi).elim⟩
    by_cases hj : p.2 = k
    · exact ⟨0,by simpa only [norm_zero] using hM,fun _ hn => (hn hj).elim⟩
    obtain ⟨H,hHn,hH⟩ := exists_double_second_holder_isometry e u hu
      (EuclideanSpace.single p.1 1) (EuclideanSpace.single p.2 1) hα (B p)
      (hB p.1 hi p.2 hj)
    exact ⟨H,hHn.trans (hBn p.1 hi p.2 hj),fun _ _ => hH⟩
  choose B' hB'n hB' using hBex
  have hflat := hrecover (e ⁻¹' S) (u ∘ e) (hu.comp e.contDiff) k
    (fun y => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (a (e y))) A' R' B' hA' (hA'n.trans hAn)
    (fun x => OAI.Analysis.PDE.Dirichlet.isometryConjugate_isSymmetric e _ (hsym ⟨e x,x.property⟩))
    (fun i hi j hj => hB' (i,j) hi hj) M Q hM hQ
    (fun i _ j _ => hB'n (i,j)) (fun i => (hR'n i).trans (hRn i))
    (fun x => by rw [OAI.Analysis.PDE.Dirichlet.inner_isometryConjugate]; exact hpos ⟨e x,x.property⟩) hR'
  have hphys := OAI.Analysis.PDE.Schauder.fourth_holder_isometry e.symm hα (u ∘ e) (hu.comp e.contDiff) hflat
  have hset : e.symm ⁻¹' (e ⁻¹' S) = S := by ext x; simp
  have hfun : (u ∘ e) ∘ e.symm = u := by funext x; simp
  rw [hset,hfun] at hphys
  exact hphys

end OAI.Analysis.PDE.Elliptic
