import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueTotal

/-! # Coefficient Residue Total Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueTotalCoordinates

noncomputable section

/-! Separate native concentration and evaluation squares for the
actual finite coefficient residue on the supported total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
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
  (k : Fin (c+g+1)) (hUk : U ≤ OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
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

def survivor (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :=
  (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)) (.up ℕ) c).map
    (CoefficientResidueAdjunctionData.survivor
      X f i j B hB U hU k hUk s hs hreg b
      (CoefficientResidueAdjunctionData.resolution X f i j B U hU k hUk) x)

def nativeSurvivor (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    (Principal.ModuleFunctor.functor U hU).obj ((ProjectiveCoefficient.HomLocal.coefficientDual X f i j B).homology c) ⟶
      Principal.ClosedKoszulResidue.target i.left U hU := by
  letI (r : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB r
  exact (Principal.ModuleHomology.complexIso U hU (ProjectiveCoefficient.HomLocal.coefficientDual X f i j B) c).inv ≫
    homologyMap
      (CoefficientResidueDimensionData.residue X f i j B U hU k hUk s hs hreg b x) c ≫
    (singleObjHomologySelfIso (.up ℕ) c (Principal.ClosedKoszulResidue.target i.left U hU)).hom

omit [AlgebraicGeometry.Flat f] [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom] in
theorem survivor_coordinates (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    survivor X f i j B hB U hU k hUk s hs hreg b x =
    (single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)) (.up ℕ) c).map
      (nativeSurvivor X f i j B hB U hU k hUk s hs hreg b x) := rfl

omit [Smooth X.hom] [IsProper X.hom] in
theorem native_concentration (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    (Supported.CechHomotopyEquivalence.functor W q).map
      (CoefficientResidueDimensionData.residue X f i j B U hU k hUk s hs hreg b x) =
    (CoefficientResidueDimensionData.concentration rfl X f i j B hB U hU W q).hom ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        (CoefficientResidueDimensionData.homologyToPrincipal
          (c := c) X f i j B U hU) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Projective.IntrinsicOverlap.Intrinsic.space R (c+g),U)) (.up ℕ) c).map
          (nativeSurvivor X f i j B hB U hU k hUk s hs hreg b x)) := by
  let (r : ℕ) := ProjectiveCoefficient.HomLocal.coefficient_dual_terms X f i j B hB r
  exact Principal.ConcentrationSingle.map_to_single U hU W (ProjectiveCoefficient.HomLocal.coefficientDual X f i j B) c
    (CoefficientResidueDimensionData.exactAt rfl X f i j B hB)
    (Principal.ClosedKoszulResidue.target i.left U hU)
    (CoefficientResidueDimensionData.residue X f i j B U hU k hUk s hs hreg b x) q

omit [Smooth X.hom] [IsProper X.hom] in
theorem concentration (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    (Supported.CechHomotopyEquivalence.functor W q).map
      (CoefficientResidueDimensionData.residue X f i j B U hU k hUk s hs hreg b x) =
    (CoefficientResidueDimensionData.concentration rfl X f i j B hB U hU W q).hom ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        (CoefficientResidueDimensionData.homologyToPrincipal
          (c := c) X f i j B U hU) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        (survivor X f i j B hB U hU k hUk s hs hreg b x) := by
  rw [survivor_coordinates]
  exact native_concentration X f i j B hB U hU k hUk s hs hreg b W q x

include hI ht hb τ in
theorem adjunction (x : Finite.FlatCoefficientSections.coefficientRing f i.left U) :
    (Supported.CechHomotopyEquivalence.functor W q).map
        (CoefficientResidueDimensionData.homMap rfl X f i j B hB U hU) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        (CoefficientResidueDimensionData.evaluation (c := c) (g := g) X f i U hU x) =
    (Supported.CechHomotopyEquivalence.functor W q).map
        (survivor X f i j B hB U hU k hUk s hs hreg b x) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        (CoefficientResidueDimensionData.symbol (c := c) X i U hU t) :=
  CoefficientResidueTotal.mappedAdjunction
    X f i j B hB U hU k hUk s hs hreg bI hI bQ t ht b hb τ W q x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueTotalCoordinates
