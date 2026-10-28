import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.HalfballBootstrap
import OAI.Analysis.PDE.Dirichlet.Moore.Matrix
import OAI.Analysis.PDE.Schauder.Calculus.TransformedValue

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "V" => CoordinateSpace n 4
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "PhysBilin" => V →L[ℝ] V →L[ℝ] ℝ
local notation "ChartSecond" => V →L[ℝ] V →L[ℝ] E

local instance residualFirstGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] Y) := inferInstance
local instance residualFirstSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] Y) := inferInstance
local instance residualSecondGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
local instance residualSecondSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) := inferInstance

/-- The actual physical quaternionic Hessian reconstructed from chart jets.
The chart space may use a different finite coordinate index from the physical
four-slot space, so no silent coordinate identification is needed. -/
def mooreChartMatrix (Bg : PhysBilin) (J : V →L[ℝ] E) (T : ChartSecond)
    (p : E →L[ℝ] ℝ) (B : Bilin) : Matrix (Fin n) (Fin n) Q :=
  OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j ↦
    Bg (coordinateVector i) (coordinateVector j) +
      (B (J (coordinateVector i)) (J (coordinateVector j)) +
        p (T (coordinateVector i) (coordinateVector j))))

def mooreChartResidual (Bg : E → PhysBilin) (J : E → V →L[ℝ] E)
    (T : E → ChartSecond) (load : E → ℝ) (p : NonlinearJet E) : ℝ :=
  OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg p.1.1) (J p.1.1) (T p.1.1) p.1.2 p.2) - load p.1.1

theorem contDiff_mooreChartResidual {k : ℕ∞ω}
    {Bg : E → PhysBilin} {J : E → V →L[ℝ] E} {T : E → ChartSecond} {load : E → ℝ}
    (hBg : ContDiff ℝ k Bg) (hJ : ContDiff ℝ k J) (hT : ContDiff ℝ k T)
    (hl : ContDiff ℝ k load) : ContDiff ℝ k (mooreChartResidual Bg J T load) := by
  let M : NonlinearJet E → Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ := fun p i j ↦
    Bg p.1.1 (coordinateVector i) (coordinateVector j) +
      (p.2 (J p.1.1 (coordinateVector i)) (J p.1.1 (coordinateVector j)) +
        p.1.2 (T p.1.1 (coordinateVector i) (coordinateVector j)))
  have hM : ContDiff ℝ k M := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    have hx : ContDiff ℝ k (fun p : NonlinearJet E ↦ p.1.1) := contDiff_fst.fst
    have hBg' := hBg.comp hx
    have hJ' := hJ.comp hx
    have hT' := hT.comp hx
    exact ((hBg'.clm_apply contDiff_const).clm_apply contDiff_const).add
      (((contDiff_snd.clm_apply (hJ'.clm_apply contDiff_const)).clm_apply
        (hJ'.clm_apply contDiff_const)).add
          (contDiff_fst.snd.clm_apply ((hT'.clm_apply contDiff_const).clm_apply contDiff_const)))
  exact ((OAI.LinearAlgebra.Moore.contDiff_mooreDet n k).comp ((hessianMatrixCLM OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff.comp hM)).sub
    (hl.comp contDiff_fst.fst)

theorem mooreChartMatrix_normal_add (Bg : PhysBilin) (J : V →L[ℝ] E) (T : ChartSecond)
    (p : E →L[ℝ] ℝ) (B : Bilin) (ℓ : E →L[ℝ] ℝ) (t : ℝ) :
    mooreChartMatrix Bg J T p (B + t • ℓ.smulRight ℓ) =
      mooreChartMatrix Bg J T p B + t • OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots
        (fun i j ↦ ℓ (J (coordinateVector i)) * ℓ (J (coordinateVector j))) := by
  let A : Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ := fun i j ↦
    Bg (coordinateVector i) (coordinateVector j) +
      (B (J (coordinateVector i)) (J (coordinateVector j)) +
        p (T (coordinateVector i) (coordinateVector j)))
  let D : Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ := fun i j ↦
    ℓ (J (coordinateVector i)) * ℓ (J (coordinateVector j))
  have he : (fun i j ↦ Bg (coordinateVector i) (coordinateVector j) +
      ((B + t • ℓ.smulRight ℓ) (J (coordinateVector i)) (J (coordinateVector j)) +
        p (T (coordinateVector i) (coordinateVector j))) :
      Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) = A + t • D := by
    ext i j
    change Bg (coordinateVector i) (coordinateVector j) +
      ((B + t • ℓ.smulRight ℓ) (J (coordinateVector i)) (J (coordinateVector j)) +
        p (T (coordinateVector i) (coordinateVector j))) = A i j + t * D i j
    dsimp only [A,D]
    simp only [add_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul]
    ring
  have hh := congrArg (hessianMatrixCLM OAI.Analysis.Calculus.Quaternion.fourSlots) he
  rw [map_add,map_smul] at hh
  exact hh

theorem mooreChartResidual_normal_symbol
    {Bg : E → PhysBilin} {J : E → V →L[ℝ] E} {T : E → ChartSecond} {load : E → ℝ}
    (p : NonlinearJet E) (ℓ : E →L[ℝ] ℝ)
    (hd : DifferentiableAt ℝ (mooreChartResidual Bg J T load) p) :
    fderiv ℝ (mooreChartResidual Bg J T load) p (0,ℓ.smulRight ℓ) =
      OAI.LinearAlgebra.Moore.mooreDifferential n (mooreChartMatrix (Bg p.1.1) (J p.1.1) (T p.1.1) p.1.2 p.2)
        (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots
          (fun i j ↦ ℓ (J p.1.1 (coordinateVector i)) * ℓ (J p.1.1 (coordinateVector j)))) := by
  let A := mooreChartMatrix (Bg p.1.1) (J p.1.1) (T p.1.1) p.1.2 p.2
  let D := OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots
    (fun i j ↦ ℓ (J p.1.1 (coordinateVector i)) * ℓ (J p.1.1 (coordinateVector j)))
  rw [← deriv_affine_line (0,ℓ.smulRight ℓ) hd]
  have he : (fun t : ℝ ↦ mooreChartResidual Bg J T load (p + t • (0,ℓ.smulRight ℓ))) =
      fun t ↦ OAI.LinearAlgebra.Moore.mooreDet n (A + t • D) - load p.1.1 := by
    funext t
    have hpath : p + t • (0,ℓ.smulRight ℓ) = ((p.1.1,p.1.2),p.2 + t • ℓ.smulRight ℓ) := by
      change (p.1 + t • 0,p.2 + t • ℓ.smulRight ℓ) = _
      simp
    rw [hpath]
    exact congrArg (fun A ↦ OAI.LinearAlgebra.Moore.mooreDet n A - load p.1.1)
      (mooreChartMatrix_normal_add _ _ _ _ _ _ _)
  rw [he]
  have hentry (i j : Fin n) : HasDerivAt (fun t : ℝ ↦ (A + t • D) i j) (D i j) 0 := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (D i j)).const_add (A i j)
  have hdet := OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_path n (fun t : ℝ ↦ A + t • D) D 0 hentry
  simpa only [zero_smul,add_zero] using (hdet.sub_const (load p.1.1)).deriv

theorem covector_coordinate_nonzero (L : V →L[ℝ] ℝ) (hL : L ≠ 0) :
    (fun i : Fin n × Fin 4 ↦ L (coordinateVector i)) ≠ 0 := by
  intro he
  apply hL
  ext x
  have hx : (∑ i, x i • coordinateVector i) = x := by
    simpa [coordinateVector] using (EuclideanSpace.basisFun (Fin n × Fin 4) ℝ).sum_repr x
  rw [← hx, map_sum]
  simp only [map_smul, zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi := congrFun he i
  simp only [Pi.zero_apply,hi,smul_zero]

theorem mooreChartResidual_normal_pos
    {Bg : E → PhysBilin} {J : E → V →L[ℝ] E} {T : E → ChartSecond} {load : E → ℝ}
    (p : NonlinearJet E) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hJ : Function.Surjective (J p.1.1))
    (hA : (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg p.1.1) (J p.1.1) (T p.1.1) p.1.2 p.2)).PosDef)
    (hd : DifferentiableAt ℝ (mooreChartResidual Bg J T load) p) :
    0 < fderiv ℝ (mooreChartResidual Bg J T load) p (0,ℓ.smulRight ℓ) := by
  rw [mooreChartResidual_normal_symbol p ℓ hd]
  let A := mooreChartMatrix (Bg p.1.1) (J p.1.1) (T p.1.1) p.1.2 p.2
  obtain ⟨C,hAC,hCA⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef A hA
  apply moore_fourSlot_principalSymbol_pos A C hA hAC hCA (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA)
  apply covector_coordinate_nonzero (ℓ.comp (J p.1.1))
  intro hz
  apply hℓ
  ext y
  obtain ⟨x,rfl⟩ := hJ y
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L x) hz

end OAI.Analysis.PDE.Dirichlet
