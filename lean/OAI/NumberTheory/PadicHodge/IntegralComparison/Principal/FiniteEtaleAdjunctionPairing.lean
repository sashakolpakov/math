import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueDimension
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionDegreeCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleFormTensor

/-! # Finite Etale Adjunction Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleAdjunctionPairing

noncomputable section

/-! The original finite adjunction followed by coefficient evaluation
is the actual coefficient residue followed by its differential symbol,
on the same supported total complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.Module Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g N : ℕ} (h : c+g=N)
attribute [local instance] MvPolynomial.gradedAlgebra
  Projective.LocalAdjunction.ambientAlgebra Projective.ParameterChart.coordinateOrder
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra
  Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (j : Fin (N+1)) (B : ℕ) (hB : N+1≤B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (q : ℕ)

private abbrev sourceForms := (Scheme.Modules.pushforward i.left).obj
  ((Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g))

private abbrev singleAt (d : ℕ) :
    ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) ⥤
      CochainComplex ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) ℕ :=
  single _ (.up ℕ) d

def finiteMap :
    (Supported.CechHomotopyEquivalence.functor W q).obj
      (ProjectiveFinite.CoefficientResidueDimensionData.sourceComplex X f.left i j B U hU) ⟶
    (Supported.CechHomotopyEquivalence.functor W q).obj
      ((singleAt U c).obj ((ModuleFunctor.functor U hU).obj
        (sourceForms (g := g) X Y f i))) :=
  (ProjectiveFinite.CoefficientResidueDimensionData.concentration h X f.left i j B hB U hU W q).hom ≫
    (Supported.CechHomotopyEquivalence.functor W q).map (ProjectiveFinite.CoefficientResidueDimensionData.homologyToPrincipal
      (c := c) X f.left i j B U hU) ≫
    (Supported.CechHomotopyEquivalence.functor W q).map ((singleAt U c).map ((ModuleFunctor.functor U hU).map
      (FiniteEtale.AdjunctionDegreeCoordinates.iso X Y f i g c (by omega) j B hB (by omega)).hom))

def pairing (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :
    (ModuleFunctor.functor U hU).obj (sourceForms (g := g) X Y f i) ⟶
      (ModuleFunctor.functor U hU).obj (ProjectiveCoefficient.HomLocal.formSheaf X i g) :=
  (ModuleFunctor.functor U hU).map (FiniteEtaleFormTensor.coefficientIso R X Y f i.left g).hom ≫
    HomEvaluation.map U hU (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g)
      (show Γ(ProjectiveCoefficient.HomLocal.coefficient X f.left i,U) from x)

theorem hom_comparison :
    (FiniteEtale.AdjunctionDegreeCoordinates.iso X Y f i g c (by omega) j B hB (by omega)).hom ≫
      (FiniteEtaleFormTensor.coefficientIso R X Y f i.left g).hom =
    (ProjectiveCoefficient.HomDegreeCoordinates.iso X f.left i g c (by omega) j B hB (by omega)).hom := by
  simpa only [FiniteEtaleFormTensor.coefficientIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] using
    FiniteEtale.AdjunctionDegreeCoordinates.coefficient_map X Y f i g c
      (by omega) j B hB (by omega)

theorem pairing_comparison (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :
    finiteMap h X Y f i j B hB U hU W q ≫ (Supported.CechHomotopyEquivalence.functor W q).map ((singleAt U c).map (pairing X Y f i U hU x)) =
      ProjectiveFinite.CoefficientResidueDimensionData.rightMap h X f.left i j B hB U hU W q x := by
  have he :
      (ModuleFunctor.functor U hU).map (FiniteEtale.AdjunctionDegreeCoordinates.iso X Y f i g c
          (by omega) j B hB (by omega)).hom ≫ pairing X Y f i U hU x =
      (ModuleFunctor.functor U hU).map (ProjectiveCoefficient.HomDegreeCoordinates.iso X f.left i g c
          (by omega) j B hB (by omega)).hom ≫
        HomEvaluation.map U hU (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g)
      (show Γ(ProjectiveCoefficient.HomLocal.coefficient X f.left i,U) from x) := by
    rw [pairing, ← Category.assoc, ← Functor.map_comp,
      hom_comparison h X Y f i j B hB]
  have hh := congrArg (fun a => (Supported.CechHomotopyEquivalence.functor W q).map
    ((singleAt U c).map a)) he
  simp only [Functor.map_comp] at hh
  simpa only [finiteMap, ProjectiveFinite.CoefficientResidueDimensionData.rightMap,
    ProjectiveFinite.CoefficientResidueDimensionData.homMap,
    ProjectiveFinite.CoefficientResidueDimensionData.evaluation, Category.assoc] using
    congrArg (fun a =>
      (ProjectiveFinite.CoefficientResidueDimensionData.concentration h X f.left i j B hB U hU W q).hom ≫
        (Supported.CechHomotopyEquivalence.functor W q).map
          (ProjectiveFinite.CoefficientResidueDimensionData.homologyToPrincipal
            (c := c) X f.left i j B U hU) ≫ a) hh

variable (k : Fin (N+1)) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (s : Fin c → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) s = Projective.LocalAdjunction.ideal X i U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (List.ofFn s))
  (bI : Basis (Fin c) (Projective.LocalAdjunction.quotient X i U hU) (Projective.LocalAdjunction.ideal X i U hU).Cotangent)
  (hI : ∀ a, bI a = (Projective.LocalAdjunction.ideal X i U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (Projective.LocalAdjunction.ideal X i U hU) s hs a))
  (bQ : Basis (Fin g) (Projective.LocalAdjunction.quotient X i U hU) Ω[Projective.LocalAdjunction.quotient X i U hU⁄R])
  (t : Fin g → Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U))
  (ht : ∀ a, bQ a = KaehlerDifferential.D R (Projective.LocalAdjunction.quotient X i U hU)
    (Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X i U hU) (t a)))
  (b : Basis (Fin N) Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) Ω[Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U)⁄R])
  (hb : (fun a : Fin (c+g) => b (Fin.cast h a)) =
    Fin.append (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (s a))
      (fun a => KaehlerDifferential.D R Γ(Projective.IntrinsicOverlap.Intrinsic.space R N, U) (t a)))
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (i.left ⁻¹ᵁ U))]

include h hB hI ht hb τ in
theorem comparison (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :
    finiteMap h X Y f i j B hB U hU W q ≫ (Supported.CechHomotopyEquivalence.functor W q).map ((singleAt U c).map (pairing X Y f i U hU x)) =
      ProjectiveFinite.CoefficientResidueDimensionData.leftMap X f.left i j B U hU k hUk
        s hs hreg t b W q x :=
  (pairing_comparison h X Y f i j B hB U hU W q x).trans
    (ProjectiveFinite.CoefficientResidueDimension.comparison h X Y.left f.left i j B hB
      U hU k hUk s hs hreg bI hI bQ t ht b hb τ W q x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleAdjunctionPairing
