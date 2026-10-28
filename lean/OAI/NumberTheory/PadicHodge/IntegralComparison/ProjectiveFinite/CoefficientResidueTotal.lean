import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomDegreeCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueLocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.FormCoherence

/-! # Coefficient Residue Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueTotal

noncomputable section

/-! The actual finite-coefficient adjunction on the supported total is
its original coefficient residue followed by the same differential symbol.
All purity comes from the finite flat projective geometry. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex

private theorem residue_factor {A : Type*} [Category A]
    {P Q S T V W : A} {r : P ⟶ T} {a : P ⟶ Q} {b : Q ⟶ S}
    {u : S ⟶ T} {v : T ⟶ W} {d : S ⟶ V} {e : V ⟶ W}
    (hr : r = a ≫ b ≫ u) (he : d ≫ e = u ≫ v) :
    r ≫ v = a ≫ b ≫ d ≫ e := by
  rw [hr]
  simp only [Category.assoc]
  rw [← he]

private theorem map_pairing {A B C : Type*} [Category A] [Category B] [Category C]
    (S : A ⥤ B) (F : B ⥤ C) {L M N Q : A}
    {a : L ⟶ N} {e : N ⟶ Q} {u : L ⟶ M} {v : M ⟶ Q}
    (h : a ≫ e = u ≫ v) :
    F.map (S.map a) ≫ F.map (S.map e) = F.map (S.map u) ≫ F.map (S.map v) := by
  simpa only [Functor.map_comp] using congrArg (fun f => F.map (S.map f)) h

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] ProjectiveCoefficient.HomLocal.scalar_terms
  ProjectiveCoefficient.HomLocal.coefficient_terms
variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (c+g)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (c+g+1)) (B : ℕ) (hB : c+g+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (c+g)).Opens) (hU : IsAffineOpen U)
  (k : Fin (c+g+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U))
  (ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (b : Basis (Fin (c+g)) Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R])
  (hb : (b : Fin (c+g) → Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R]) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g), U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]

variable {ι : Type u} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (q : ℕ)

include hI ht hb τ in
abbrev mappedAdjunction (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
  map_pairing
    (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)) (.up ℕ) c)
    (Supported.CechHomotopyEquivalence.functor (R := Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)) W q)
    (CoefficientResidueAdjunction.comparison
      X f i j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ x)

include hI ht hb τ in
abbrev rawComparison (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
  residue_factor
    (CoefficientResidueConcentration.concentration
      X f i j B hB U hU k hUk s hs hreg b W q x)
    (mappedAdjunction X f i j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ W q x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueTotal
