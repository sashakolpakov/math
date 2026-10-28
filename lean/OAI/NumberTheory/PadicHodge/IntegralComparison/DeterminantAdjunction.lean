import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalAdjunction
import Mathlib.LinearAlgebra.Pi

/-! # Determinant Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantAdjunction

noncomputable section

/-! The adjunction between conormal and ambient determinant lines is
independent of the chosen conormal basis. Its source is the actual Hom
module between determinant lines, so the determinant factors cancel. -/

open _root_.Module
open scoped TensorProduct

universe u v w t

open OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

section Evaluation

variable {A : Type u} [CommRing A]
  {U : Type v} [AddCommGroup U] [Module A U]
  {V : Type w} [AddCommGroup V] [Module A V]
  {W : Type t} [AddCommGroup W] [Module A W]
  {c : ℕ} (b : Basis (Fin c) A U)

def evaluation : ((⋀[A]^c U) →ₗ[A] V) ≃ₗ[A] V :=
  ((TopExteriorCoordinates.equiv b).arrowCongr (LinearEquiv.refl A V)).trans
    (LinearMap.ringLmapEquivSelf A A V)

@[simp]
theorem evaluation_apply (φ : (⋀[A]^c U) →ₗ[A] V) : evaluation b φ = φ (TopExteriorCoordinates.generator b) := by
  change φ ((TopExteriorCoordinates.equiv b).symm 1) = φ (TopExteriorCoordinates.generator b)
  rw [TopExteriorCoordinates.equiv_symm_apply, one_smul]

theorem generator_change (b' : Basis (Fin c) A U) :
    TopExteriorCoordinates.generator b' = b.det b' • TopExteriorCoordinates.generator b := by
  have h := TopExteriorCoordinates.reconstruct b (TopExteriorCoordinates.generator b')
  rw [TopExteriorCoordinates.generator, TopExteriorCoordinates.coordinate_wedge] at h
  exact h.symm

def ofResidue (r : V ≃ₗ[A] W) : ((⋀[A]^c U) →ₗ[A] V) ≃ₗ[A] W :=
  (evaluation b).trans r

@[simp]
theorem ofResidue_apply (r : V ≃ₗ[A] W) (φ : (⋀[A]^c U) →ₗ[A] V) :
    ofResidue b r φ = r (φ (TopExteriorCoordinates.generator b)) := by
  simp only [ofResidue, LinearEquiv.trans_apply, evaluation_apply]

theorem ofResidue_change (b' : Basis (Fin c) A U) (r r' : V ≃ₗ[A] W)
    (hr : r.toLinearMap = b.det b' • r'.toLinearMap) : ofResidue b r = ofResidue b' r' := by
  ext φ
  rw [ofResidue_apply, ofResidue_apply, generator_change b b', map_smul, map_smul]
  exact LinearMap.congr_fun hr (φ (TopExteriorCoordinates.generator b))

end Evaluation

section Split

variable {A : Type u} [CommRing A]
  {U : Type v} [AddCommGroup U] [Module A U]
  {W : Type w} [AddCommGroup W] [Module A W]
  {V : Type t} [AddCommGroup V] [Module A V]
  {c g : ℕ} (bU : Basis (Fin c) A U) (bW : Basis (Fin g) A W)
  (e : (U × W) ≃ₗ[A] V)

def split : ((⋀[A]^c U) →ₗ[A] ⋀[A]^(c + g) V) ≃ₗ[A] ⋀[A]^g W :=
  ofResidue bU (SplitExteriorAdjunction.residue bU bW e)

theorem split_conormal_basis (bU' : Basis (Fin c) A U) : split bU bW e = split bU' bW e :=
  ofResidue_change bU bU' _ _ (ConormalAdjunction.residue_conormal_basis bU bU' bW e)

theorem split_quotient_basis (bW' : Basis (Fin g) A W) : split bU bW e = split bU bW' e := by
  unfold split
  rw [SplitExteriorAdjunction.residue_independent_quotient_basis bU bW e bW']

theorem split_splitting (e' : (U × W) ≃ₗ[A] V)
    (hU : ∀ u, e (u, 0) = e' (u, 0))
    (hW : ∀ v, (e.symm v).2 = (e'.symm v).2) : split bU bW e = split bU bW e' := by
  unfold split
  rw [SplitExteriorAdjunction.residue_independent_splitting bU bW e e' hU hW]

end Split

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  [Algebra.Smooth k R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
  {c g : ℕ} (bI : Basis (Fin c) (R ⧸ I) I.Cotangent)
  (bQ : Basis (Fin g) (R ⧸ I) Ω[R ⧸ I⁄k])

def conormal :
    ((⋀[R ⧸ I]^c I.Cotangent) →ₗ[R ⧸ I] ⋀[R ⧸ I]^(c + g) ((R ⧸ I) ⊗[R] Ω[R⁄k])) ≃ₗ[R ⧸ I]
      ⋀[R ⧸ I]^g Ω[R ⧸ I⁄k] :=
  ofResidue bI (ConormalAdjunction.equivalence I bI bQ)

theorem conormal_basis (bI' : Basis (Fin c) (R ⧸ I) I.Cotangent) :
    conormal I bI bQ = conormal I bI' bQ :=
  ofResidue_change bI bI' _ _ (ConormalAdjunction.conormal_basis I bI bQ bI')

theorem quotient_basis (bQ' : Basis (Fin g) (R ⧸ I) Ω[R ⧸ I⁄k]) :
    conormal I bI bQ = conormal I bI bQ' := by
  unfold conormal
  rw [ConormalAdjunction.independent_quotient_basis I bI bQ bQ']

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantAdjunction
