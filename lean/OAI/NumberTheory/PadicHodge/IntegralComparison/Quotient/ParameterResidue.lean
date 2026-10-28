import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalParameterResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalAdjunction

/-! # Parameter Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterResidue

noncomputable section

/-! The original quotient conormal adjunction takes the literal normal
differentials followed by lifted parameters to their quotient symbol. -/
open _root_.Module
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
  [Algebra.Smooth k A] (I : Ideal A) [Algebra.Smooth k (A ⧸ I)]
  {c g : ℕ} (bI : Basis (Fin c) (A ⧸ I) I.Cotangent)
  (s : Fin c → I) (hs : ∀ i, bI i = I.toCotangent (s i))
  (bQ : Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k]) (t : Fin g → A)
  (ht : ∀ i, bQ i = KaehlerDifferential.D k (A ⧸ I) (Ideal.Quotient.mk I (t i)))

def normalWedge : ⋀[A ⧸ I]^(c + g) ((A ⧸ I) ⊗[A] Ω[A⁄k]) :=
  exteriorPower.ιMulti (A ⧸ I) (c + g)
    (Fin.append (fun i => (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D k A (s i).val)
      (fun i => (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D k A (t i)))

def normalParameters : Fin c → (ConormalAdjunction.presentation (k := k) I).ker :=
  fun i => ⟨(s i).val, Ideal.Quotient.eq_zero_iff_mem.mpr (s i).property⟩

include hs in
omit [Algebra.Smooth k A] [Algebra.Smooth k (A ⧸ I)] in
theorem conormal_basis (i : Fin c) :
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) i =
      Algebra.Extension.Cotangent.mk (normalParameters (k := k) I s i) := by
  apply (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).injective
  rw [Basis.map_apply, LinearEquiv.apply_symm_apply, hs i]
  rfl

include hs ht in
theorem wedge : ConormalAdjunction.equivalence (k := k) I bI bQ (normalWedge I s t) =
    exteriorPower.ιMulti (A ⧸ I) g
      (fun i => KaehlerDifferential.D k (A ⧸ I) (Ideal.Quotient.mk I (t i))) := by
  let P := ConormalAdjunction.presentation (k := k) I
  let : Algebra.Smooth k P.Ring := inferInstanceAs (Algebra.Smooth k A)
  exact ConormalParameterResidue.wedge P
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm)
    (normalParameters (k := k) I s) (conormal_basis I bI s hs) bQ t ht

include hs ht in
theorem symbol (a : A ⧸ I) :
    ConormalAdjunction.equivalence (k := k) I bI bQ (a • normalWedge I s t) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior k (A ⧸ I) g
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k (A ⧸ I) a
          (fun i => Ideal.Quotient.mk I (t i))) := by
  rw [map_smul, wedge I bI s hs bQ t ht,
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterResidue
