import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameBaseChange

/-! # Parameter Line Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ParameterLineAdjunction

noncomputable section

/-! A frame given by the actual ordered parameter wedge makes the
line-valued conormal adjunction the literal quotient differential symbol. -/
open _root_.CategoryTheory _root_.Module
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
  (I : Ideal A) {c g : ℕ} (s : Fin c → I) (t : Fin g → A)
  (b : Basis (Fin (c + g)) A Ω[A⁄k])
  (hb : (b : Fin (c + g) → Ω[A⁄k]) =
    Fin.append (fun i => KaehlerDifferential.D k A (s i).val)
      (fun i => KaehlerDifferential.D k A (t i)))
  (N : ModuleCat.{u} A) (e : N ≃ₗ[A] ⋀[A]^(c + g) Ω[A⁄k])

def frame : N ≅ ModuleCat.of A A :=
  (e.trans (TopExteriorCoordinates.equiv b)).toModuleIso

def ambient : ((A ⧸ I) ⊗[A] N) ≃ₗ[A ⧸ I]
    ⋀[A ⧸ I]^(c + g) ((A ⧸ I) ⊗[A] Ω[A⁄k]) :=
  (e.baseChange A (A ⧸ I) N _).trans (TopExteriorBaseChange.equiv (A ⧸ I) b)

theorem frame_inv : e ((frame b N e).inv 1) = exteriorPower.ιMulti A (c + g) b := by
  change e (e.symm ((TopExteriorCoordinates.equiv b).symm 1)) = _
  rw [LinearEquiv.apply_symm_apply, TopExteriorCoordinates.equiv_symm_apply, one_smul]
  rfl

include hb in
theorem ambient_frame (a : A ⧸ I) :
    ambient I b N e ((LineValuedKoszulPurity.lineFrame A I N (frame b N e)).symm a) =
      a • IntegralComparison.Quotient.ParameterResidue.normalWedge I s t := by
  rw [LineFrameBaseChange.lineFrame_symm_tmul]
  change TopExteriorBaseChange.equiv (A ⧸ I) b (a ⊗ₜ[A] e ((frame b N e).inv 1)) = _
  rw [frame_inv, TopExteriorBaseChange.equiv_tmul_ιMulti, hb]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left, Fin.append_right]

variable [Algebra.Smooth k A] [Algebra.Smooth k (A ⧸ I)]
  (bI : Basis (Fin c) (A ⧸ I) I.Cotangent)
  (hs : ∀ i, bI i = I.toCotangent (s i))
  (bQ : Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k])
  (ht : ∀ i, bQ i = KaehlerDifferential.D k (A ⧸ I) (Ideal.Quotient.mk I (t i)))

include hb hs ht in
theorem residue (a : A ⧸ I) :
    ConormalAdjunction.equivalence I bI bQ
      (ambient I b N e ((LineValuedKoszulPurity.lineFrame A I N (frame b N e)).symm a)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior k (A ⧸ I) g
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k (A ⧸ I) a
          (fun i => Ideal.Quotient.mk I (t i))) := by
  rw [ambient_frame I s t b hb N e]
  exact IntegralComparison.Quotient.ParameterResidue.symbol I bI s hs bQ t ht a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ParameterLineAdjunction
