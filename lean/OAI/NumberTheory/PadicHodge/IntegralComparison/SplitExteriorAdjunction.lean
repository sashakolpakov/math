import OAI.NumberTheory.PadicHodge.IntegralComparison.SplitTopForm
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

/-! # Split Exterior Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction

noncomputable section

/-! Top exterior powers of a split exact sequence admit the usual
adjunction map after choosing a conormal basis. It is independent of
both the splitting and the auxiliary quotient basis. -/

open _root_.Module

universe u v w t

variable {R : Type u} [CommRing R]
  {U : Type v} [AddCommGroup U] [Module R U]
  {W : Type w} [AddCommGroup W] [Module R W]
  {V : Type t} [AddCommGroup V] [Module R V]
  {c g : ℕ} (bU : Basis (Fin c) R U) (bW : Basis (Fin g) R W)

def productBasis (e : (U × W) ≃ₗ[R] V) : Basis (Fin (c + g)) R V :=
  ((bU.prod bW).map e).reindex finSumFinEquiv

theorem prod_basis_det (bU' : Basis (Fin c) R U) (bW' : Basis (Fin g) R W) :
    (bU.prod bW).det (bU'.prod bW') = bU.det bU' * bW.det bW' := by
  let a := (bU.equiv bU' (Equiv.refl _)).toLinearMap
  let d := (bW.equiv bW' (Equiv.refl _)).toLinearMap
  let T : (U × W) →ₗ[R] U × W := a.prodMap d
  have hT : T ∘ (bU.prod bW) = (bU'.prod bW' : _ → U × W) := by
    funext i
    cases i <;> ext <;> simp [T, a, d, Basis.prod_apply]
  rw [← hT, Basis.det_comp, Basis.det_self, mul_one]
  rw [SplitTopForm.det_eq_mul bU bW T a d (by intro u; simp [T])
    (by intro z; rfl)]
  rw [Basis.det_basis, Basis.det_basis]

theorem productBasis_det (e : (U × W) ≃ₗ[R] V)
    (bU' : Basis (Fin c) R U) (bW' : Basis (Fin g) R W) :
    (productBasis bU bW e).det (productBasis bU' bW' e) = bU.det bU' * bW.det bW' := by
  rw [productBasis, Basis.det_reindex, Basis.det_map]
  convert prod_basis_det bU bW bU' bW' using 1
  congr 1
  funext i
  simp [productBasis, Function.comp_def]

def residue (e : (U × W) ≃ₗ[R] V) : (⋀[R]^(c + g) V) ≃ₗ[R] ⋀[R]^g W :=
  (TopExteriorCoordinates.equiv (productBasis bU bW e)).trans
    (TopExteriorCoordinates.equiv bW).symm

theorem residue_apply (e : (U × W) ≃ₗ[R] V) (x : ⋀[R]^(c + g) V) :
    residue bU bW e x =
      TopExteriorCoordinates.coordinate (productBasis bU bW e) x •
        TopExteriorCoordinates.generator bW := rfl

theorem residue_generator (e : (U × W) ≃ₗ[R] V) :
    residue bU bW e (TopExteriorCoordinates.generator (productBasis bU bW e)) =
      TopExteriorCoordinates.generator bW := by
  rw [residue_apply, TopExteriorCoordinates.coordinate_generator, one_smul]

theorem residue_independent_splitting (e f : (U × W) ≃ₗ[R] V)
    (hU : ∀ u, e (u, 0) = f (u, 0))
    (hW : ∀ v, (e.symm v).2 = (f.symm v).2) :
    residue bU bW e = residue bU bW f := by
  have hdet : (productBasis bU bW e).det = (productBasis bU bW f).det := by
    simp only [productBasis, Basis.det_reindex']
    rw [SplitTopForm.topForm_eq bU bW e f hU hW]
  have hc := TopExteriorCoordinates.coordinate_eq (productBasis bU bW e) hdet
  ext x
  simp only [residue_apply]
  rw [hc]

theorem residue_independent_quotient_basis (e : (U × W) ≃ₗ[R] V)
    (bW' : Basis (Fin g) R W) : residue bU bW e = residue bU bW' e := by
  have hgen : residue bU bW e (TopExteriorCoordinates.generator (productBasis bU bW e)) =
      residue bU bW' e (TopExteriorCoordinates.generator (productBasis bU bW e)) := by
    rw [residue_generator, residue_apply]
    have hc : TopExteriorCoordinates.coordinate (productBasis bU bW' e)
        (TopExteriorCoordinates.generator (productBasis bU bW e)) = bW'.det bW := by
      rw [TopExteriorCoordinates.generator, TopExteriorCoordinates.coordinate_wedge,
        productBasis_det, Basis.det_self, one_mul]
    rw [hc]
    simpa only [TopExteriorCoordinates.generator, TopExteriorCoordinates.coordinate_wedge]
      using (TopExteriorCoordinates.reconstruct bW'
        (TopExteriorCoordinates.generator bW)).symm
  ext x
  conv_lhs => rw [← TopExteriorCoordinates.reconstruct (productBasis bU bW e) x]
  conv_rhs => rw [← TopExteriorCoordinates.reconstruct (productBasis bU bW e) x]
  rw [map_smul, map_smul, hgen]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction
