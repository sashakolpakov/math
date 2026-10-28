import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MooreResidual
import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetActual

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder

namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace
attribute [local instance] residualFirstGroup residualFirstSpace
  residualSecondGroup residualSecondSpace

variable {n : ℕ} {Z E W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

local notation "V" => CoordinateSpace n 4
local notation "PhysBilin" => V →L[ℝ] V →L[ℝ] ℝ
local notation "ChartSecond" => V →L[ℝ] V →L[ℝ] E

/-- The actual Moore residual with external parameters. Only the spatial
two-jet is passed to the quaternionic Hessian reconstruction. -/
def parameterMooreResidual (Bg : Z × E → PhysBilin)
    (J : Z × E → V →L[ℝ] E) (T : Z × E → ChartSecond)
    (load : Z × E → ℝ) (p : Z × NonlinearJet E) : ℝ :=
  mooreChartResidual (fun x => Bg (p.1,x)) (fun x => J (p.1,x))
    (fun x => T (p.1,x)) (fun x => load (p.1,x)) p.2

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem parameterMooreResidual_apply
    (Bg : Z × E → PhysBilin) (J : Z × E → V →L[ℝ] E)
    (T : Z × E → ChartSecond) (load : Z × E → ℝ)
    (z : Z) (j : NonlinearJet E) :
    parameterMooreResidual Bg J T load (z,j) =
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg (z,j.1.1)) (J (z,j.1.1))
        (T (z,j.1.1)) j.1.2 j.2) - load (z,j.1.1) := rfl

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The residual evaluated on an actual spatial two-jet is precisely the
chart-form Moore equation for that spatial slice. -/
theorem parameterMooreResidual_twoJet
    (Bg : Z × E → PhysBilin) (J : Z × E → V →L[ℝ] E)
    (T : Z × E → ChartSecond) (load : Z × E → ℝ)
    (f : Z × E → ℝ) (z : Z) (x : E) :
    parameterMooreResidual Bg J T load
      (z,nonlinearTwoJet (fun y => f (z,y)) x) =
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg (z,x)) (J (z,x)) (T (z,x))
        (fderiv ℝ (fun y => f (z,y)) x)
        (fderiv ℝ (fderiv ℝ (fun y => f (z,y))) x)) - load (z,x) := rfl

/-- Smooth dependence of the actual matrix/determinant residual, including
mixed external-parameter and spatial-jet derivatives. -/
theorem contDiff_parameterMooreResidual {k : ℕ∞ω}
    {Bg : Z × E → PhysBilin} {J : Z × E → V →L[ℝ] E}
    {T : Z × E → ChartSecond} {load : Z × E → ℝ}
    (hBg : ContDiff ℝ k Bg) (hJ : ContDiff ℝ k J)
    (hT : ContDiff ℝ k T) (hl : ContDiff ℝ k load) :
    ContDiff ℝ k (parameterMooreResidual Bg J T load) := by
  let M : Z × NonlinearJet E →
      Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ := fun p a b =>
    Bg (p.1,p.2.1.1) (coordinateVector a) (coordinateVector b) +
      (p.2.2 (J (p.1,p.2.1.1) (coordinateVector a))
        (J (p.1,p.2.1.1) (coordinateVector b)) +
      p.2.1.2 (T (p.1,p.2.1.1) (coordinateVector a) (coordinateVector b)))
  have hx : ContDiff ℝ k (fun p : Z × NonlinearJet E => (p.1,p.2.1.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst.fst
  have hM : ContDiff ℝ k M := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro b
    have hb := hBg.comp hx
    have hj := hJ.comp hx
    have ht := hT.comp hx
    exact ((hb.clm_apply contDiff_const).clm_apply contDiff_const).add
      (((contDiff_snd.snd.clm_apply (hj.clm_apply contDiff_const)).clm_apply
        (hj.clm_apply contDiff_const)).add
        (contDiff_snd.fst.snd.clm_apply
          ((ht.clm_apply contDiff_const).clm_apply contDiff_const)))
  exact ((OAI.LinearAlgebra.Moore.contDiff_mooreDet n k).comp
    ((hessianMatrixCLM OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff.comp hM)).sub (hl.comp hx)

/-- The same smoothness assertion is local in the true base point. In
particular coefficients only defined smoothly near a closed patch suffice. -/
theorem contDiffAt_parameterMooreResidual {k : ℕ∞ω}
    {Bg : Z × E → PhysBilin} {J : Z × E → V →L[ℝ] E}
    {T : Z × E → ChartSecond} {load : Z × E → ℝ}
    (p : Z × NonlinearJet E)
    (hBg : ContDiffAt ℝ k Bg (p.1,p.2.1.1))
    (hJ : ContDiffAt ℝ k J (p.1,p.2.1.1))
    (hT : ContDiffAt ℝ k T (p.1,p.2.1.1))
    (hl : ContDiffAt ℝ k load (p.1,p.2.1.1)) :
    ContDiffAt ℝ k (parameterMooreResidual Bg J T load) p := by
  let M : Z × NonlinearJet E →
      Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ := fun p a b =>
    Bg (p.1,p.2.1.1) (coordinateVector a) (coordinateVector b) +
      (p.2.2 (J (p.1,p.2.1.1) (coordinateVector a))
        (J (p.1,p.2.1.1) (coordinateVector b)) +
      p.2.1.2 (T (p.1,p.2.1.1) (coordinateVector a) (coordinateVector b)))
  have hx : ContDiffAt ℝ k (fun p : Z × NonlinearJet E => (p.1,p.2.1.1)) p :=
    (contDiff_fst.prodMk contDiff_snd.fst.fst).contDiffAt
  have hM : ContDiffAt ℝ k M p := by
    apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    have hb := hBg.comp p hx
    have hj := hJ.comp p hx
    have ht := hT.comp p hx
    exact ((hb.clm_apply contDiffAt_const).clm_apply contDiffAt_const).add
      (((contDiff_snd.snd.contDiffAt.clm_apply (hj.clm_apply contDiffAt_const)).clm_apply
        (hj.clm_apply contDiffAt_const)).add
        (contDiff_snd.fst.snd.contDiffAt.clm_apply
          ((ht.clm_apply contDiffAt_const).clm_apply contDiffAt_const)))
  exact ((OAI.LinearAlgebra.Moore.contDiff_mooreDet n k).contDiffAt.comp p
    ((hessianMatrixCLM OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff.contDiffAt.comp p hM)).sub (hl.comp p hx)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Exact spatial principal symbol of the parameter-dependent residual. -/
theorem parameterMooreResidual_slice_normal_symbol
    {Bg : Z × E → PhysBilin} {J : Z × E → V →L[ℝ] E}
    {T : Z × E → ChartSecond} {load : Z × E → ℝ}
    (z : Z) (j : NonlinearJet E) (k : E →L[ℝ] ℝ)
    (hd : DifferentiableAt ℝ (fun a => parameterMooreResidual Bg J T load (z,a)) j) :
    fderiv ℝ (fun a => parameterMooreResidual Bg J T load (z,a)) j
        (0,k.smulRight k) =
      OAI.LinearAlgebra.Moore.mooreDifferential n (mooreChartMatrix (Bg (z,j.1.1)) (J (z,j.1.1))
        (T (z,j.1.1)) j.1.2 j.2)
        (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun a b =>
          k (J (z,j.1.1) (coordinateVector a)) *
          k (J (z,j.1.1) (coordinateVector b)))) := by
  exact mooreChartResidual_normal_symbol (n := n) (E := E)
    (Bg := fun x => Bg (z,x)) (J := fun x => J (z,x))
    (T := fun x => T (z,x)) (load := fun x => load (z,x)) j k hd

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Positivity is needed only in the spatial normal direction. The external
parameters acquire no artificial ellipticity assumption. -/
theorem parameterMooreResidual_slice_normal_pos
    {Bg : Z × E → PhysBilin} {J : Z × E → V →L[ℝ] E}
    {T : Z × E → ChartSecond} {load : Z × E → ℝ}
    (z : Z) (j : NonlinearJet E) (k : E →L[ℝ] ℝ) (hk : k ≠ 0)
    (hJ : Function.Surjective (J (z,j.1.1)))
    (hA : (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg (z,j.1.1)) (J (z,j.1.1))
      (T (z,j.1.1)) j.1.2 j.2)).PosDef)
    (hd : DifferentiableAt ℝ (fun a => parameterMooreResidual Bg J T load (z,a)) j) :
    0 < fderiv ℝ (fun a => parameterMooreResidual Bg J T load (z,a)) j
      (0,k.smulRight k) := by
  exact mooreChartResidual_normal_pos (n := n) (E := E)
    (Bg := fun x => Bg (z,x)) (J := fun x => J (z,x))
    (T := fun x => T (z,x)) (load := fun x => load (z,x)) j k hk hJ hA hd

/-- Normal positivity for the residual on an arbitrary enlarged ambient
space, after projection to the spatial two-jet. -/
theorem parameterMooreResidual_lift_normal_pos
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    {Bg : Z × E → PhysBilin} {J : Z × E → V →L[ℝ] E}
    {T : Z × E → ChartSecond} {load : Z × E → ℝ}
    (j : NonlinearJet W) (ℓ : W →L[ℝ] ℝ) (k : E →L[ℝ] ℝ)
    (hℓ : ℓ.comp i = k) (hk : k ≠ 0)
    (hJ : Function.Surjective (J (p j.1.1,q j.1.1)))
    (hA : (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix
      (Bg (p j.1.1,q j.1.1)) (J (p j.1.1,q j.1.1))
      (T (p j.1.1,q j.1.1))
      (spatialGradientRestriction i j.1.2) (spatialHessianRestriction i j.2))).PosDef)
    (hd : DifferentiableAt ℝ (parameterMooreResidual Bg J T load)
      (parameterJetProjection p q i j)) :
    0 < fderiv ℝ (parameterResidual p q i (parameterMooreResidual Bg J T load))
      j (0,ℓ.smulRight ℓ) := by
  rw [parameterResidual_normal_symbol_slice p q i _ j ℓ k hℓ hd]
  have hds := hd.comp (parameterJetProjection p q i j).2
    ((differentiableAt_const (parameterJetProjection p q i j).1).prodMk differentiableAt_id)
  simp only [parameterJetProjection_apply] at hds ⊢
  exact parameterMooreResidual_slice_normal_pos (n := n) (E := E)
    (Bg := Bg) (J := J) (T := T) (load := load) (p j.1.1)
    ((q j.1.1,spatialGradientRestriction i j.1.2),spatialHessianRestriction i j.2)
    k hk hJ hA hds

end OAI.Analysis.PDE.Dirichlet
