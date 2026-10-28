import OAI.NumberTheory.PadicHodge.IntegralComparison.SplitResidueArbitraryLifts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalRank
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo

/-! # Conormal Parameter Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalParameterResidue

noncomputable section

/-! The genuine smooth conormal sequence sends the wedge of normal
equations and lifted quotient parameters to the literal quotient
differential symbol, with coefficient one and no sign. -/
open _root_.Module
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
  (P : Algebra.Extension k B) [Algebra.Smooth k P.Ring] [Algebra.Smooth k B]
  {c g : ℕ} (bI : Basis (Fin c) B P.Cotangent) (s : Fin c → P.ker)
  (hs : ∀ i, bI i = Algebra.Extension.Cotangent.mk (s i))
  (bQ : Basis (Fin g) B Ω[B⁄k]) (t : Fin g → P.Ring)
  (ht : ∀ i, bQ i = KaehlerDifferential.D k B (algebraMap P.Ring B (t i)))

def normalWedge : ⋀[B]^(c + g) P.CotangentSpace :=
  exteriorPower.ιMulti B (c + g)
    (Fin.append (fun i => (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (s i).val)
      (fun i => (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (t i)))

include hs ht in
theorem wedge : SplitExteriorAdjunction.residue bI bQ
    (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm (normalWedge P s t) =
      exteriorPower.ιMulti B g (fun i => KaehlerDifferential.D k B (algebraMap P.Ring B (t i))) := by
  have hi (i : Fin c) : (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm (bI i, 0) =
      (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (s i).val := by
    rw [IntegralComparison.Smooth.ConormalRank.SplitNormalization.inl, hs i, Algebra.Extension.cotangentComplex_mk]
  have hq (i : Fin g) :
      (IntegralComparison.Smooth.ConormalRank.differentialSplit P
        ((1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (t i))).2 = bQ i := by
    rw [IntegralComparison.Smooth.ConormalRank.SplitNormalization.snd, ht i]
    exact (KaehlerDifferential.mapBaseChange_tmul ..).trans (by simp)
  have h := SplitResidueArbitraryLifts.residue_wedge bI bQ
    (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm
    (fun i => (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (t i)) hq
  rw [show (fun i => (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm (bI i, 0)) =
    (fun i => (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (s i).val) from funext hi,
    show (bQ : Fin g → Ω[B⁄k]) =
      (fun i => KaehlerDifferential.D k B (algebraMap P.Ring B (t i))) from funext ht] at h
  exact h

include hs ht in
theorem symbol (a : B) : SplitExteriorAdjunction.residue bI bQ
    (IntegralComparison.Smooth.ConormalRank.differentialSplit P).symm (a • normalWedge P s t) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior k B g
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k B a
          (fun i => algebraMap P.Ring B (t i))) := by
  rw [map_smul, wedge P bI s hs bQ t ht, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalParameterResidue
