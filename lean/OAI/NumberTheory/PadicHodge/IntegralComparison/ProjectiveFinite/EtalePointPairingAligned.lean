import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingCoordinates

/-! # Etale Point Pairing Aligned -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingAligned

noncomputable section

/-! The coefficient pairing, joined through its separately checked native residue coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n c g : ℕ} (hcg : c+g=n+1)
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n+2≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ ((s₀ ≫ f.left) ≫ i.left) ⁻¹ᵁ U)
  (k : Fin (n+2)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
  (ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) s t =
    ((s₀ ≫ f.left) ≫ i.left).ker.ideal ⟨U,hU⟩)
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (List.ofFn (Fin.append s t)))
  (b : Basis (Fin (n+1)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)⁄R])
  (hb : (fun a : Fin (c+g) => b (Fin.cast hcg a)) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]

attribute [local instance] EtalePointPairingData.composite_smooth
  EtalePointPairingData.composite_proper EtalePointPairingData.composite_connected
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingData

private theorem join {A : Type*} {a b c d e f : A}
    (hab : a = b) (hcd : c = d) (hef : e = f) (hbc : b = c) (hde : d = e) : a = f :=
  hab.trans (hbc.trans (hcd.trans (hde.trans hef)))

abbrev comparison (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := by
  have hp := EtalePointPairingData.pairingPoint (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
    (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
    (k := k) (hUk := hUk) (s := s) (hs := hs) (hreg := hreg)
    (bI := bI) (hI := hI) (bQ := bQ) (t := t) (ht := ht) (hst := hst)
    (b := b) (hb := hb) (τ := τ) x
  have hr := EtalePointPairingData.weightedResidue (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
    (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
    (hcontains := hcontains) (k := k) (hUk := hUk) (s := s) (hs := hs) (hreg := hreg)
    (t := t) (hst := hst) (hregst := hregst) (b := b) x
  have hm := EtalePointPairingCoordinates.image (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
      (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
      (k := k) (hUk := hUk) (s := s) (hs := hs) (hreg := hreg) (t := t) (hst := hst) (b := b) x
  exact join hp hm hr (by as_aux_lemma => rfl) (by as_aux_lemma => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingAligned
