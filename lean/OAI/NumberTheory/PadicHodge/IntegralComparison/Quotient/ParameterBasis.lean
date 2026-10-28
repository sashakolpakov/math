import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantBasisNeighborhood

/-! # Parameter Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterBasis

noncomputable section

/-! Normal equations and lifted quotient parameters give the prescribed
ambient differential basis after quotient. Its determinant is a unit
along the entire smooth closed chart. -/
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

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalAdjunction.presentation (k := k) I
local instance presentation_smooth : Algebra.Smooth k (P).Ring :=
  inferInstanceAs (Algebra.Smooth k A)

def basis : Basis (Fin (c + g)) (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄k]) :=
  SplitExteriorAdjunction.productBasis
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) bQ
    (SplitResidueArbitraryLifts.adapted bQ
      (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm
      (fun i => (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D k A (t i)))

include hs ht in
theorem basis_eq : (basis I bI bQ t : Fin (c + g) → (A ⧸ I) ⊗[A] Ω[A⁄k]) =
    Fin.append (fun i => (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D k A (s i).val)
      (fun i => (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D k A (t i)) := by
  have hq (i : Fin g) :
      (IntegralComparison.Smooth.ConormalRank.differentialSplit P
        ((1 : A ⧸ I) ⊗ₜ[(P).Ring] KaehlerDifferential.D k (P).Ring (t i))).2 = bQ i := by
    rw [IntegralComparison.Smooth.ConormalRank.SplitNormalization.snd, ht i]
    exact (KaehlerDifferential.mapBaseChange_tmul ..).trans (by
      simp only [one_smul, KaehlerDifferential.map_D]
      rfl)
  have h := SplitResidueArbitraryLifts.productBasis_append
    (bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) bQ
    (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm
    (fun i => (1 : A ⧸ I) ⊗ₜ[(P).Ring] KaehlerDifferential.D k (P).Ring (t i)) hq
  have hi : (fun i => (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm
      ((bI.map (AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I).symm) i, 0)) =
      (fun i => (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D k A (s i).val) := by
    funext i
    rw [IntegralComparison.Smooth.ConormalRank.SplitNormalization.inl,
      ParameterResidue.conormal_basis I bI s hs,
      Algebra.Extension.cotangentComplex_mk]
    rfl
  rw [hi] at h
  exact h

include hs ht in
theorem determinant_isUnit (b : Basis (Fin (c + g)) A Ω[A⁄k]) :
    IsUnit (Ideal.Quotient.mk I
      (b.det (Fin.append (fun i => KaehlerDifferential.D k A (s i).val)
        (fun i => KaehlerDifferential.D k A (t i))))) := by
  apply DeterminantBasisNeighborhood.image_isUnit b _ (A ⧸ I) (basis I bI bQ t)
  intro i
  rw [basis_eq I bI s hs bQ t ht]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ParameterBasis
