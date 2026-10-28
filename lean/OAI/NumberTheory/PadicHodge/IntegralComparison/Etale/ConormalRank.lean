import OAI.NumberTheory.PadicHodge.IntegralComparison.DualCoordinateConormalBasis
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ExtendedQuotient
import Mathlib.RingTheory.Etale.Kaehler

/-! # Conormal Rank -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalRank

noncomputable section

/-! The rank of the genuine conormal module is unchanged on an étale
ambient neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry KaehlerDifferential

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.Etale R S]

theorem quotient_etale (I : Ideal R) :
    Algebra.Etale (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  have hbase : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have h := MorphismProperty.of_isPullback (P := @Etale)
    (AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange.Construction.affineQuotient_baseChange_isPullback (S := S) I).flip hbase
  exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h)

variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k S]
  [IsScalarTower k R S] [Algebra.Smooth k R] [IsNoetherianRing R]
  (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]

include k in
theorem rank_eq (q : PrimeSpectrum (S ⧸ I.map (algebraMap R S))) :
    Module.rankAtStalk (I.map (algebraMap R S)).Cotangent q =
      Module.rankAtStalk I.Cotangent
        (q.comap (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))) := by
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : Algebra.Smooth k (S ⧸ I.map (algebraMap R S)) := AlgebraicGeometry.Resolution.Blowups.Smooth.ExtendedQuotient.Construction.smooth_extended_quotient I
  let : Algebra.Etale (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := quotient_etale I
  let : IsScalarTower k (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I
  rw [IntegralComparison.Smooth.ConormalRank.quotient_rank_sub (k := k),
    IntegralComparison.Smooth.ConormalRank.quotient_rank_sub (k := k)]
  have h₁ := Module.rankAtStalk_isBaseChange
    (KaehlerDifferential.isBaseChange_of_formallyEtale k R S)
    (q.comap (Ideal.Quotient.mk (I.map (algebraMap R S))))
  have h₂ := Module.rankAtStalk_isBaseChange
    (KaehlerDifferential.isBaseChange_of_formallyEtale k (R ⧸ I)
      (S ⧸ I.map (algebraMap R S))) q
  rw [h₁, h₂]
  congr 2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (z : ι → I.map (algebraMap R S)) (D : ι → Derivation k S S)
  (hD : ∀ i j, D i (z j).val = if i = j then 1 else 0)
  (hgen : Ideal.span (Set.range (fun i => (z i).val)) = I.map (algebraMap R S))

include hD hgen in
theorem cardinal_eq_rank (q : PrimeSpectrum (S ⧸ I.map (algebraMap R S))) :
    Fintype.card ι = Module.rankAtStalk I.Cotangent
      (q.comap (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))) := by
  rw [← rank_eq (k := k) I q]
  exact (DualCoordinateConormalBasis.rankAtStalk _ z D hD hgen q).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalRank
