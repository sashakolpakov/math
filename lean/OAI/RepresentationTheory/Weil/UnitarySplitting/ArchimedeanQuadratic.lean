import OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport

/-! # Archimedean Quadratic -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadratic.Construction

noncomputable section

/-! Quadratic phases preserve the actual test space in real field coordinates. -/

open _root_.MeasureTheory
open scoped BigOperators SchwartzMap

theorem real_quadratic_temperate {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) :
    Function.HasTemperateGrowth (Local.FunctionsMetaplectic.Construction.quadratic B) := by
  have hc (i : Fin d) : Function.HasTemperateGrowth (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d => x i) :=
    (ContinuousLinearMap.proj i : Local.FunctionsMetaplectic.Construction.Position ℝ d →L[ℝ] ℝ).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth
      (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d => ∑ i, ∑ j, x i * B i j * x j) :=
    .sum (fun i _ => .sum (fun j _ => ((hc i).mul (.const (B i j))).mul (hc j)))
  exact hq.mul (.const (2 : ℝ)⁻¹)

theorem real_quadratic_mem {d : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (B : Matrix (Fin d) (Fin d) ℝ) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d := by
  obtain ⟨φ, hφ⟩ := (RealChartTestSpace.Construction.schwartzBruhat_realChart_iff (ContinuousAddEquiv.refl _)).mp f.property
  let θ := SchwartzMap.smulLeftCLM ℂ (fun x => ψ (Local.FunctionsMetaplectic.Construction.quadratic B x)) φ
  apply (RealChartTestSpace.Construction.schwartzBruhat_realChart_iff (ContinuousAddEquiv.refl _)).mpr
  refine ⟨θ, ?_⟩
  funext x
  rw [Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, hφ]
  exact (SchwartzMap.smulLeftCLM_apply_apply
    ((RealCharacter.Construction.continuous_unitary_real_character_temperate ψ hc hu).comp
      (real_quadratic_temperate B)) φ x).symm

variable {F : Type} [NormedField F] {d : ℕ}
variable (e : ℝ ≃+* F) (he : Continuous e) (hei : Continuous e.symm)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1)

theorem quadratic_field_coordinates (B : Matrix (Fin d) (Fin d) F) (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    Local.FunctionsMetaplectic.Construction.quadratic B (FieldCoordinates.Construction.coordinateFieldEquiv (Fin d) e he hei x) =
      e (Local.FunctionsMetaplectic.Construction.quadratic (fun i j => e.symm (B i j)) x) := by
  simp only [Local.FunctionsMetaplectic.Construction.quadratic, map_div₀, map_ofNat, map_sum, map_mul, e.apply_symm_apply]
  rfl

include e he hei hc hu in
theorem archimedean_quadratic_mem (B : Matrix (Fin d) (Fin d) F)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  let a := FieldCoordinates.Construction.coordinateFieldEquiv (Fin d) e he hei
  let χ := ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  have hm := real_quadratic_mem χ (hc.comp he) (fun t => hu (e t))
    (fun i j => e.symm (B i j)) (FieldCoordinates.Construction.crossFieldTestEquiv a f)
  have hp := FieldCoordinates.Construction.schwartzBruhat_comp_cross_addEquiv a.symm hm
  convert hp using 1
  funext x
  change ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x =
    ψ (e (Local.FunctionsMetaplectic.Construction.quadratic (fun i j => e.symm (B i j)) (a.symm x))) * f.val (a (a.symm x))
  rw [a.apply_symm_apply, ← quadratic_field_coordinates e he hei]
  change ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x = ψ (Local.FunctionsMetaplectic.Construction.quadratic B (a (a.symm x))) * f.val x
  rw [a.apply_symm_apply]

def archimedeanQuadraticOperator (B : Matrix (Fin d) (Fin d) F) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun f := ⟨Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val, archimedean_quadratic_mem e he hei ψ hc hu B f⟩
  invFun f := ⟨Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-B) f.val, archimedean_quadratic_mem e he hei ψ hc hu (-B) f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change ψ (Local.FunctionsMetaplectic.Construction.quadratic (-B) x) * (ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x) = f.val x
    rw [Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * (ψ (Local.FunctionsMetaplectic.Construction.quadratic (-B) x) * f.val x) = f.val x
    rw [Local.FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  map_add' f g := Subtype.ext ((Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_add f.val g.val)
  map_smul' a f := Subtype.ext ((Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_smul a f.val)

theorem archimedeanQuadraticOperator_unitary
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    (B : Matrix (Fin d) (Fin d) F) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d (archimedeanQuadraticOperator e he hei ψ hc hu B f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  unfold Local.FunctionsMetaplectic.Construction.l2Energy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ‖ψ (Local.FunctionsMetaplectic.Construction.quadratic B x) * f.val x‖ ^ 2 = ‖f.val x‖ ^ 2
    rw [norm_mul, hu, one_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadratic.Construction
