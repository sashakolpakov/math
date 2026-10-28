import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalKoszulPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityTargetFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantAdjunction
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Line Valued Koszul Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineValuedKoszulPurity

noncomputable section

/-! Oriented purity with its actual target line. Evaluation on the
conormal determinant is valued in the scalar extension of that line. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (I : Ideal R) (N : ModuleCat.{u} R)
  (e : N ≅ ModuleCat.of R R)

def lineFrame : ((R ⧸ I) ⊗[R] N) ≃ₗ[R ⧸ I] (R ⧸ I) :=
  (e.toLinearEquiv.baseChange R (R ⧸ I) N R).trans
    (TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I))

theorem lineFrame_tmul (a : R ⧸ I) (x : N) :
    lineFrame R I N e (a ⊗ₜ[R] x) = a * Ideal.Quotient.mk I (e.hom x) := by
  change (TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I))
    (a ⊗ₜ[R] e.hom x) = _
  simp [Algebra.smul_def, mul_comm]

theorem lineFrame_scale (e' : N ≅ ModuleCat.of R R) (r : R) (h : e'.hom = r • e.hom)
    (x : (R ⧸ I) ⊗[R] N) :
    lineFrame R I N e' x = Ideal.Quotient.mk I r * lineFrame R I N e x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul a x =>
      rw [lineFrame_tmul, lineFrame_tmul]
      have hx := congrArg (fun f : N ⟶ ModuleCat.of R R => f x) h
      change e'.hom x = r * e.hom x at hx
      rw [hx, map_mul]
      ring

variable {n : ℕ} (s : Fin n → R)
  (hs : Koszul.OrientedTopCohomology.ideal R s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))
  (b : Module.Basis (Fin n) (R ⧸ I) I.Cotangent)

abbrev source :=
  (((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
    (ComplexShape.down ℕ).symm).obj P.complex.op).homology n)

abbrev target := ModuleCat.of R
  ((⋀[R ⧸ I]^n I.Cotangent) →ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] N))

def iso : source R I N P (n := n) ≅ target R I N (n := n) :=
  LinearHomOrientedPurity.iso R I s hs hreg P N e ≪≫
    ((lineFrame R I N e).symm.restrictScalars R).toModuleIso ≪≫
      ((DeterminantAdjunction.evaluation (V := (R ⧸ I) ⊗[R] N) b).symm.restrictScalars R).toModuleIso

theorem evaluated (x : source R I N P (n := n)) :
    (DeterminantAdjunction.evaluation b)
      ((iso R I N e s hs hreg P b).hom x) =
        (lineFrame R I N e).symm
          ((LinearHomOrientedPurity.iso R I s hs hreg P N e).hom x) := by
  exact (DeterminantAdjunction.evaluation b).apply_symm_apply _

theorem normalized (x : source R I N P (n := n)) :
    lineFrame R I N e ((DeterminantAdjunction.evaluation b)
      ((iso R I N e s hs hreg P b).hom x)) =
        (LinearHomOrientedPurity.iso R I s hs hreg P N e).hom x := by
  rw [evaluated, LinearEquiv.apply_symm_apply]

theorem independent_target_frame (e' : N ≅ ModuleCat.of R R) :
    iso R I N e s hs hreg P b = iso R I N e' s hs hreg P b := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (DeterminantAdjunction.evaluation b).injective
  apply (lineFrame R I N e').injective
  rw [lineFrame_scale R I N e e' _ (OrientedPurityTargetFrame.frame_scalar R N e e'),
    normalized, normalized]
  exact (congrArg (fun f => f x)
    (OrientedPurityTargetFrame.purity_frame R N e e' I s hs hreg P)).symm

variable (hb : ∀ i, b i = I.toCotangent (ConormalKoszulPurity.conormalVectors R I s hs i))
  (t : Fin n → R) (ht : Koszul.OrientedTopCohomology.ideal R t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn t))
  (bt : Module.Basis (Fin n) (R ⧸ I) I.Cotangent)
  (hbt : ∀ i, bt i = I.toCotangent (ConormalKoszulPurity.conormalVectors R I t ht i))

include hb hbt in
theorem independent_generators : iso R I N e s hs hreg P b = iso R I N e t ht htreg P bt := by
  obtain ⟨A, hA⟩ := ConormalKoszulPurity.exists_change_matrix R I s hs t ht
  have hd : bt.det b = Ideal.Quotient.mk I A.det := by
    have h := Koszul.GeneratorMatrix.conormal_determinant I
      (ConormalKoszulPurity.conormalVectors R I s hs)
      (ConormalKoszulPurity.conormalVectors R I t ht) bt hbt A hA
    simpa only [← hb] using h
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (DeterminantAdjunction.evaluation b).injective
  apply (lineFrame R I N e).injective
  rw [normalized]
  have heval (φ : (⋀[R ⧸ I]^n I.Cotangent) →ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] N)) :
      DeterminantAdjunction.evaluation b φ =
        bt.det b • DeterminantAdjunction.evaluation bt φ := by
    rw [DeterminantAdjunction.evaluation_apply, DeterminantAdjunction.evaluation_apply,
      DeterminantAdjunction.generator_change bt b, map_smul]
  rw [heval, map_smul, normalized, hd]
  exact congrArg (fun f => f x)
    (LinearHomOrientedPurity.transition R I s hs hreg P N e t ht htreg A hA)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineValuedKoszulPurity
