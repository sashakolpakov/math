import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointPairingAligned
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueDataAnnihilation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FiniteEtaleResidueDetection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalAdjunctionDimensionData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.SectionEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ResidueReferenceValue

/-! # Etale Point Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointResidue

noncomputable section

/-! The actual finite local point class is a selected source residue.
Both trace pairings and scalar annihilation are derived from the original
fixed point and the genuine projective parameter chart. -/
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
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i.left ⁻¹ᵁ U))
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

local instance composite_smooth : Smooth (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change Smooth (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance
local instance composite_proper : IsProper (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change IsProper (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance
local instance composite_connected : GeometricallyConnected (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) := by
  change GeometricallyConnected (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom)
  rw [Over.w i]
  infer_instance

include i hbase in
omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
private theorem pointClosed : IsClosedImmersion (s₀ ≫ f.left) := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  exact isClosedImmersion_of_comp_eq_id (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) (s₀ ≫ f.left)
    (FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase)

private def scalarValue
    (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU) :
    (Principal.FiniteEtaleResidueDetection.ambientFunctor U
      (PrincipalPoint.Fraction.family U D.parameters) D.codimension (D.codimension+g)).obj
        (Principal.SectionPresheaf.modules U hU (ProjectivePoint.KoszulMap.scalar i.left)) := by
  letI : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  exact ProjectivePoint.ResidueData.residue X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction R Y X f s₀ hbase) B hB U hU D

private def finiteValue :
    (Principal.FiniteEtaleResidueDetection.ambientFunctor U
      (PrincipalPoint.Fraction.family U t) c (c+g)).obj
        (Principal.SectionPresheaf.modules U hU ((Scheme.Modules.pushforward i.left).obj
          (FiniteEtale.FormSheafDuality.source R Y X f g))) := by
  letI : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  letI := Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
  letI := Finite.MapPureTrace.coefficients_finiteType f.left i.left
  exact Principal.FiniteEtaleAdjunctionPairing.finiteMap hcg X Y f i
    (ProjectivePoint.Survivor.chart (R := R) (n := n)) B hB U hU
    (PrincipalPoint.Fraction.family U t) (c+g)
    (ProjectivePoint.CoefficientLocalClass.value i.left (s₀ ≫ f.left)
      (FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase) B hB
      (Cech.StructurePullbackUnit.coefficients f.left i.left)
      (Cech.SectionCoefficientUnit.sheafMap s₀ f.left i.left) U hU s t hst hcg)

private abbrev parameterData : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU :=
  { coordinate := k
    below_coordinate := hUk
    contains := hcontains
    codimension := c
    dimension := hcg
    equations := s
    generates := hs
    regular := hreg
    conormalBasis := bI
    conormalBasis_apply := hI
    parameters := t
    quotientBasis := bQ
    quotientBasis_apply := ht
    point_generates := hst
    point_regular := hregst
    coordinateIndex := τ
    finiteVariables := inferInstance
    coordinates := inferInstance
    coordinateTower := inferInstance
    coordinateEtale := inferInstance
    ambientBasis := b
    ambientBasis_apply := hb }

omit [SmoothOfRelativeDimension g X.hom] in
omit [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
private theorem scalar_annihilated
    (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
    (v : Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
    (hv : v ∈ ((s₀ ≫ f.left) ≫ i.left).ker.ideal ⟨U,hU⟩) :
    v • scalarValue (X := X) (Y := Y) (f := f) (i := i)
      (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU) D = 0 := by
  let : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  exact ProjectivePoint.ResidueDataAnnihilation.annihilated X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction R Y X f s₀ hbase) B hB U hU D v hv

private theorem pairing_align {A : Type*} {a b c d : A}
    (h : a = b) (ha : c = a) (hb : b = d) : c = d :=
  ha.trans (h.trans hb)

local instance pairingTargetBase : Algebra R (Finite.FlatCoefficientSections.quotientRing i.left U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
local instance pairingSourceBase : Algebra R (Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))

omit [Nonempty ↥X.left] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
private theorem pairing_data
    (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
    (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :
    (Principal.FiniteEtaleResidueDetection.ambientFunctor U
      (PrincipalPoint.Fraction.family U D.parameters) D.codimension (D.codimension+g)).map
      ((Principal.ModuleFunctor.functor U hU).map
          (Principal.FiniteEtaleFormTensor.coefficientIso R X Y f i.left g).hom ≫
        Principal.HomEvaluation.map U hU (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) x)
      (finiteValue (hcg := D.dimension) (X := X) (Y := Y) (f := f) (i := i)
        (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
        (s := D.equations) (t := D.parameters) (hst := D.point_generates)) =
    algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
      (Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains x) •
      (Principal.FiniteEtaleResidueDetection.ambientFunctor U
        (PrincipalPoint.Fraction.family U D.parameters) D.codimension (D.codimension+g)).map
        (Principal.PushforwardSection.map i.left U hU
          (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
          (Integral.FormSectionUnit.unit R X g (i.left ⁻¹ᵁ U)
            (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (Finite.FlatCoefficientSections.quotientRing i.left U) 1
              (fun a => i.left.app U (D.parameters a)))))
        (scalarValue (X := X) (Y := Y) (f := f) (i := i)
          (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU) D) := by
  let := D.finiteVariables
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  have h := EtalePointPairingAligned.comparison D.dimension X Y f i s₀ hbase B hB
    U hU D.contains D.coordinate D.below_coordinate D.equations D.generates D.regular
    D.conormalBasis D.conormalBasis_apply D.quotientBasis D.parameters D.quotientBasis_apply
    D.point_generates D.point_regular D.ambientBasis D.ambientBasis_apply D.coordinateIndex x
  let : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  have hn := ProjectivePoint.ResidueReferenceValue.Reference.comparison X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction R Y X f s₀ hbase) B hB U hU D
  have hr := congrArg (fun y =>
    algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)
      (Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains x) •
    (Supported.CechHomotopyEquivalence.functor
      (R := Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)) (PrincipalPoint.Fraction.family U D.parameters)
      (D.codimension+g)).map
      ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤
        ModuleCat.{u} Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)) (.up ℕ) D.codimension).map
        (Principal.DifferentialSymbol.map R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i U hU g
          (fun a => i.left.app U (D.parameters a)))) y) hn
  refine pairing_align h ?_ ?_
  · as_aux_lemma => rfl
  · refine pairing_align hr ?_ ?_
    · as_aux_lemma => rfl
    · as_aux_lemma => rfl

abbrev formulas := by
  let hsec := FiniteEtale.SectionUnit.section_over X Y f i s₀ hbase
  let hsX := SectionEvaluationNaturality.image_retraction R Y X f s₀ hbase
  let hpoint : ((s₀ ≫ f.left) ≫ i.left) ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)).hom = 𝟙 _ :=
    (Category.assoc _ _ _).trans hsec
  letI : IsClosedImmersion (s₀ ≫ f.left) := pointClosed
    (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀) (hbase := hbase)
  letI : Algebra R (Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
  letI : Algebra R (Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
  letI := Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) hcontains
  let ε := Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) hcontains
  let W := PrincipalPoint.Fraction.family U t
  let F := Principal.FiniteEtaleResidueDetection.ambientFunctor U W c (c+g)
  let D := parameterData (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i) (s₀ := s₀)
    (U := U) (hU := hU) (hcontains := hcontains) (k := k) (hUk := hUk)
    (s := s) (hs := hs) (hreg := hreg) (bI := bI) (hI := hI) (bQ := bQ)
    (t := t) (ht := ht) (hst := hst) (hregst := hregst) (b := b) (hb := hb) (τ := τ)
  let r := scalarValue (X := X) (Y := Y) (f := f) (i := i)
    (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU) D
  let a := finiteValue (hcg := hcg) (X := X) (Y := Y) (f := f) (i := i)
    (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU)
    (s := s) (t := t) (hst := hst)
  let ω := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (Finite.FlatCoefficientSections.quotientRing i.left U) 1 (fun v => i.left.app U (t v))
  have hlift (v : R) :
      algebraMap (Finite.FlatCoefficientSections.quotientRing i.left U) R (i.left.app U (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) v)) = v := by
    change Intrinsic.SectionEvaluation.evaluation R X (s₀ ≫ f.left) hsX
      (i.left ⁻¹ᵁ U) hcontains (i.left.app U (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) v)) = v
    rw [SectionEvaluationNaturality.pullback R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i (s₀ ≫ f.left) hsX U hcontains]
    exact (Intrinsic.SectionEvaluation.evaluation R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
      ((s₀ ≫ f.left) ≫ i.left) hpoint U hcontains).commutes v
  have hscalar (v : Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U))
      (hv : algebraMap (Finite.FlatCoefficientSections.quotientRing i.left U) R (i.left.app U v) = 0) : v • r = 0 := by
    have he := SectionEvaluationNaturality.pullback R X (Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) i
      (s₀ ≫ f.left) hsX U hcontains v
    change Intrinsic.SectionEvaluation.evaluation R X (s₀ ≫ f.left) hsX
      (i.left ⁻¹ᵁ U) hcontains (i.left.app U v) = 0 at hv
    have hz : Intrinsic.SectionEvaluation.evaluation R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
        ((s₀ ≫ f.left) ≫ i.left) hpoint U hcontains v = 0 := he.symm.trans hv
    have hk : v ∈ ((s₀ ≫ f.left) ≫ i.left).ker.ideal ⟨U,hU⟩ := by
      rw [← Intrinsic.SectionEvaluation.kernel R (Projective.IntrinsicOverlap.Intrinsic.model R (n+1))
        ((s₀ ≫ f.left) ≫ i.left) hpoint U hcontains hU]
      exact hz
    exact scalar_annihilated (X := X) (Y := Y) (f := f) (i := i)
      (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU) D v hk
  have hpair (x : Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :
      F.map ((Principal.ModuleFunctor.functor U hU).map
          (Principal.FiniteEtaleFormTensor.coefficientIso R X Y f i.left g).hom ≫
        Principal.HomEvaluation.map U hU (ProjectiveCoefficient.HomLocal.coefficient X f.left i) (ProjectiveCoefficient.HomLocal.formSheaf X i g) x) a =
      algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U) (ε x) •
        F.map (Principal.PushforwardSection.map i.left U hU
          (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
          (Integral.FormSectionUnit.unit R X g (i.left ⁻¹ᵁ U) ω)) r := by
    exact pairing_data (X := X) (Y := Y) (f := f) (i := i)
      (s₀ := s₀) (hbase := hbase) (B := B) (hB := hB) (U := U) (hU := hU) D x
  exact And.intro
    (Principal.FiniteEtaleResidueDetection.exists_residue R X Y f i.left U hU hgood g W c (c+g)
      ε (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)) hlift ω r a hscalar hpair)
    (Principal.FiniteEtaleResidueDetection.eq_residue R X Y f i.left U hU hgood g W c (c+g)
      ε (algebraMap R Γ(Projective.IntrinsicOverlap.Intrinsic.space R (n+1), U)) hlift ω r a hscalar hpair)

abbrev exists_residue :=
  (formulas hcg X Y f i s₀ hbase B hB U hU hcontains hgood k hUk s hs hreg
    bI hI bQ t ht hst hregst b hb τ).1

abbrev eq_residue :=
  (formulas hcg X Y f i s₀ hbase B hB U hU hcontains hgood k hUk s hs hreg
    bI hI bQ t ht hst hregst b hb τ).2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointResidue
