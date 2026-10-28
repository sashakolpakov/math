import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedCoefficientResidueClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueClass

/-! # Coefficient Residue Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueClass

noncomputable section

/-! The original finite coefficient resolution, evaluated on a section,
uses the same supported point residue as the scalar resolution. The
coefficient changes only its canonical weight. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem refinement_isIso
    {C : Type u} [Preorder C] [HasFiniteProducts C]
    {A : Type u} [CommRing A] {ι : Type u} [LinearOrder ι] (W : ι → C)
    {K L T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} A) ℕ}
    (eK : HomotopyEquiv K T) (eL : HomotopyEquiv L T) (a : K ⟶ L)
    (ha : Homotopy (a ≫ eL.hom) eK.hom) (q : ℕ) :
    IsIso ((Supported.CechHomotopyEquivalence.functor W q).map a) := by
  rw [← Supported.CechHomotopyEquivalence.refinementIso_hom W eK eL a ha q]
  infer_instance

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPointFraction
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R)) [IsClosedImmersion i]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y) [IsClosedImmersion (s₀ ≫ f)]
  (hbase : (s₀ ≫ f) ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
  (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens) (hU : IsAffineOpen U)
  (hcontains : ⊤ ≤ ((s₀ ≫ f) ≫ i) ⁻¹ᵁ U)
  (j : Fin (n+2)) (hj : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
  (e : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (ProjectivePoint.Survivor.chart (R := R)) (n+2), U) ≃ₗ[
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)]
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  {c m : ℕ} (s : Fin c → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (t : Fin m → Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s = i.ker.ideal ⟨U,hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s t =
    ((s₀ ≫ f) ≫ i).ker.ideal ⟨U,hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn s))
  (hregst : RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U)
    (List.ofFn (Fin.append s t)))

local instance sectionAlgebra : Algebra R Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R
    (Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2)))) U

local instance coefficients_qc : (CoefficientPointFraction.coefficients f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i
local instance coefficients_finite : (CoefficientPointFraction.coefficients f i).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f i
local instance line_qc : (ProjectivePoint.ScalarFraction.line (R := R) (n := n)).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible (ProjectivePoint.Survivor.chart (R := R)) (n+2))

abbrev weight (x : Finite.FlatCoefficientSections.coefficientRing f i U) := by
  letI := FiniteCoefficient.QuotientAction.algebra f i U hU s hs
  letI := FiniteCoefficient.QuotientAction.tower f i U hU s hs
  exact Projective.FixedCoefficientPointFraction.scalar i (s₀ ≫ f) hbase
    (CoefficientPointFraction.coefficients f i) (Cech.SectionCoefficientUnit.sheafMap s₀ f i)
    U hU hcontains s t hst (Finite.FlatCoefficientSections.coefficientRing f i U) (Finite.FlatCoefficientSections.chartIso f i U hU) x

abbrev residueMap (x : Finite.FlatCoefficientSections.coefficientRing f i U) := by
  letI := FiniteCoefficient.QuotientAction.algebra f i U hU s hs
  letI := FiniteCoefficient.QuotientAction.tower f i U hU s hs
  letI (q : ℕ) := Affine.ProjectiveResolutionTerms.term_projective U hU j hj
    (CoefficientPointFraction.coefficients f i) (ProjectivePoint.Survivor.chart (R := R)) B q
  exact Principal.CoefficientResidueData.map U hU
    (ProjectivePoint.ScalarFraction.line (R := R) (n := n)) e
    (CoefficientPointFraction.coefficients f i) (CoefficientPointFraction.source f i B) (CoefficientPointFraction.augmentation f i B)
    (ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Finite.FlatCoefficientSections.coefficientRing f i U))
    (Finite.FlatCoefficientSections.chartIso f i U hU) (CoefficientPointFraction.resolution f i B U hU j hj) i s hs hreg
    (Koszul.CoefficientPointFraction.vector
      Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s (Finite.FlatCoefficientSections.coefficientRing f i U) x)

abbrev rawComparison (x : Finite.FlatCoefficientSections.coefficientRing f i U)
    (y : (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t)
      (c+m)).obj (ProjectivePoint.LocalCoordinates.principalDual i (s₀ ≫ f) B U hU)) := by
  letI := FiniteCoefficient.QuotientAction.algebra f i U hU s hs
  letI := FiniteCoefficient.QuotientAction.tower f i U hU s hs
  let W := PrincipalPoint.Fraction.family U t
  let M := CoefficientPointFraction.coefficients f i
  let v := Cech.SectionCoefficientUnit.sheafMap s₀ f i
  let T := ModuleCat.of Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Finite.FlatCoefficientSections.coefficientRing f i U)
  let eM := Finite.FlatCoefficientSections.chartIso f i U hU
  let PM := CoefficientPointFraction.resolution f i B U hU j hj
  let β := Koszul.CoefficientPointFraction.vector
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) s (Finite.FlatCoefficientSections.coefficientRing f i U) x
  let w := weight f i s₀ hbase U hU hcontains s t hst x
  let hw := Projective.FixedCoefficientPointFraction.weight i (s₀ ≫ f) hbase
    M v U hU hcontains s t hst (Finite.FlatCoefficientSections.coefficientRing f i U) eM x
  let ev := ProjectiveCoefficient.PointFraction.evaluation U hU s hreg T PM β
  let hr := ProjectiveCoefficient.PointFraction.rightCoordinates
    i (s₀ ≫ f) B M v U hU j hj e s t hst hregst T eM PM
  let hl := ProjectiveCoefficient.PointFraction.leftCoordinates
    i (s₀ ≫ f) B M v U hU j hj e T eM PM
  let he := ProjectiveCoefficient.PointFraction.evaluationHomotopy
    i (s₀ ≫ f) M v U hU s t hst hreg hregst T eM PM β w hw
  letI := refinement_isIso W _ _ _ hl (c+m)
  have h := Koszul.RefinedCoefficientResidueClass.actual_residue
    Γ(Proj (homogeneousSubmodule (Fin (n+2)) R), U) (Principal.SectionPresheaf.rings U hU)
    W s t (PrincipalPoint.Fraction.units U hU t) _ _ _ _ _ ev hr w he
    R (Principal.TerminalScalars.bijective U hU) (n+1)
    (ProjectivePoint.ScalarFraction.pure i (s₀ ≫ f) hbase B hB U hU)
    (ProjectivePoint.ScalarFraction.zero i (s₀ ≫ f) hbase B hB U hU s t hst)
    (ProjectivePoint.ScalarFraction.pointQuotient i (s₀ ≫ f) hbase U hU hcontains s t hst)
    (Principal.ClosedKoszulResidue.target i U hU)
    (Principal.ClosedKoszulResidue.pullback i U hU s hs)
    (Principal.ClosedKoszulResidue.annihilated i U hU s hs) _ hl y
  exact h

abbrev comparison (x : Finite.FlatCoefficientSections.coefficientRing f i U)
    (y : (Supported.CechHomotopyEquivalence.functor (PrincipalPoint.Fraction.family U t)
      (c+m)).obj (ProjectivePoint.LocalCoordinates.principalDual i (s₀ ≫ f) B U hU)) :=
  rawComparison f i s₀ hbase B hB U hU hcontains j hj e s t hs hst hreg hregst x y

variable [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] (hcm : c+m=n+1)

abbrev fixedPoint (x : Finite.FlatCoefficientSections.coefficientRing f i U) :=
  comparison f i s₀ hbase B hB U hU hcontains j hj e s t hs hst hreg hregst x
    (ProjectivePoint.LocalCoordinates.pointAt i (s₀ ≫ f) hbase B hB U hU s t hst hcm)

abbrev fixedPoint_scalar (x : Finite.FlatCoefficientSections.coefficientRing f i U) := by
  have h := fixedPoint f i s₀ hbase B hB U hU hcontains j hj e s t hs hst hreg hregst hcm x
  have hscalar := ProjectivePoint.ResidueClass.fixedPoint
    i (s₀ ≫ f) hbase B hB U hU hcontains j hj e s t hs hst hreg hregst hcm
  exact h.trans (congrArg
    (fun z => weight f i s₀ hbase U hU hcontains s t hst x • z) hscalar.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientResidueClass
