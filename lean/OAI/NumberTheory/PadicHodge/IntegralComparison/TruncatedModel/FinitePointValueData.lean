import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FiniteSelectedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SelectedFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterOpenEtale
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SerreGlobal

/-! # Finite Point Value Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValueData

noncomputable section

/-! The original finite point class has the same signed local residue
value after restriction to the selected component. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join_equalities {A : Type*} {a b c d : A}
    (hab : a = b) (hcd : c = d) (hbc : b = c) : a = d :=
  hab.trans (hbc.trans hcd)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) [IsNoetherianRing (Truncated.Witt.Ring p k n)]
  [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)]
  [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] {d g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom] [SmoothOfRelativeDimension g Y.hom]
  (s₀ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : d+2≤B) (U : (Projective.IntrinsicOverlap.Intrinsic.space (Truncated.Witt.Ring p k n) (d+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
  (hgood : FiniteEtale.TraceBasis.Good (Truncated.Witt.Ring p k n) Y X f (i.left ⁻¹ᵁ U))
  (z : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U)
  (hz :
    letI : Algebra (Truncated.Witt.Ring p k n) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X (i.left ⁻¹ᵁ U)
    letI : Algebra (Truncated.Witt.Ring p k n) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra (Truncated.Witt.Ring p k n) X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) := f.left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AffineOpen.DeRhamTrace.sectionEtale (Truncated.Witt.Ring p k n) Y X f (i.left ⁻¹ᵁ U) hgood.1
    (1 ⊗ₜ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U] z : (Truncated.Witt.Ring p k n) ⊗[IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U] IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) =
      FiniteEtale.FiberSectionTrace.component (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) (Truncated.Witt.Ring p k n)
        (IntegralComparison.Finite.SectionEvaluation.evaluation (Truncated.Witt.Ring p k n) X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains))
  (he :
    letI : Algebra (Truncated.Witt.Ring p k n) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X (i.left ⁻¹ᵁ U)
    letI : Algebra (Truncated.Witt.Ring p k n) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra (Truncated.Witt.Ring p k n) X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
    IntegralComparison.Finite.SectionEvaluation.evaluation (Truncated.Witt.Ring p k n) X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains z = 1)

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

variable (Z : Over (Spec (CommRingCat.of k))) [IsSeparated Z.hom] (j : Z.left ⟶ Y.left)
  (hp : IsPullback j Z.hom Y.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Z) n))

abbrev selectedOpen : Y.left.affineOpens :=
  ⟨Y.left.basicOpen z, FiniteEtale.SelectedSourceRecovery.selectedAffine X Y f i U hgood z⟩
include hgood in
abbrev selectedBelow : (selectedOpen p k n X Y f i U hgood z).val ≤ (f ≫ i).left ⁻¹ᵁ U :=
  FiniteEtale.SelectedSourceRecovery.selectedBelow X Y f i U z
abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) Y g
abbrev cover := SerreGlobal.Finite.cover p k n X Y f i
abbrev coverFull := SerreGlobal.Finite.coverFull p k n X Y f i
abbrev coverAffine := Intrinsic.RefinedTransferTrace.inverseCover_affine
  (Truncated.Witt.Ring p k n) Y X f (Intrinsic.TopFormTrace.cover X i)
  (Intrinsic.TopFormTrace.cover_affine X i)
abbrev outside := SectionIdealPuncturedCover.outside s₀.ker
abbrev conditions := FiniteEtale.SelectedSourceRecovery.supportConditions X Y f i s₀ hbase U hU D hgood z hz
abbrev parameters := TransportedPrincipalData.Fraction.parameters (f ≫ i).left U
  (selectedOpen p k n X Y f i U hgood z) (selectedBelow p k n X Y f i U hgood z) g D.parameters

abbrev nativeClass := PrincipalSource.ClassCoordinates.nativeClass f.left i.left U hU
  (form (g := g) p k n Y) D.parameters D.codimension (Y.left.basicOpen z)
  (selectedOpen p k n X Y f i U hgood z).property (selectedBelow p k n X Y f i U hgood z)
  (FiniteEtale.SelectedSourceRecovery.selectedClass X Y f i s₀ hbase B hB U hU D z)

abbrev nativeMap := TransportedPrincipalData.Fraction.nativeComparison p k n Y (f ≫ i).left U hU
  (selectedOpen p k n X Y f i U hgood z) (selectedBelow p k n X Y f i U hgood z) g D.parameters
  (outside p k n Y s₀) (cover p k n X Y f i) (coverFull p k n X Y f i) (coverAffine p k n X Y f i)
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_affine
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_punctured
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_cover
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_global D.codimension

include he in
abbrev native_recovery := by
  have hr := FiniteEtale.SelectedSourceRecovery.native_recovery X Y f i s₀ hbase B hB U hU D hgood z hz he
  have hm := IntrinsicCoordinates.IntrinsicComparison.selected p k n Y g U hU D.parameters D.codimension
    (cover p k n X Y f i) (coverFull p k n X Y f i) (coverAffine p k n X Y f i) f.left i.left z
    (PrincipalPoint.PulledIntegerRefinement.outside f.left (s₀ ≫ f.left)) (outside p k n Y s₀)
    (conditions p k n X Y f i s₀ hbase U hU D hgood z hz)
    (selectedOpen p k n X Y f i U hgood z).property (selectedBelow p k n X Y f i U hgood z)
  exact join_equalities hr
    (congrArg (fun a => a (nativeClass p k n X Y f i s₀ hbase B hB U hU D hgood z)) hm)
    (by as_aux_lemma => rfl)

def tracePoint : FiniteEtale.ProperTraceBase.cohomology X Y f i g :=
  FiniteEtale.SectionClassData.sectionClass X Y f i s₀ hbase B hB g

omit [Fintype k] [CharP k p] [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] [SmoothOfRelativeDimension g X.hom] [SmoothOfRelativeDimension g Y.hom] in
theorem output_map :
    SerreGlobal.Finite.output p k n X Y f i g D.codimension =
      PrincipalPoint.Source.Comparison.sourceOutput (c := D.codimension) (g := g)
        f.left i.left (FiniteEtale.SelectedSourceRecovery.baseMap (R := Truncated.Witt.Ring p k n) (n := d))
        (FiniteEtale.SelectedSourceRecovery.cover (R := Truncated.Witt.Ring p k n) (n := d))
        (form (g := g) p k n Y) := rfl

def evaluate (x : (Affine.OrderedInjective.Comparison.source (form (g := g) p k n Y) D.codimension
    (cover p k n X Y f i)).homology (g+D.codimension)) :
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Z) n (g+g) :=
  PrincipalSheafFraction.value p k n Y Z j hp I g D.codimension
    (cover p k n X Y f i) (coverFull p k n X Y f i) (ULift.up.{2,1} (ULift.up.{1,0} x))

def pointValue : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Z) n (g+g) :=
  evaluate p k n X Y f i s₀ U hU D Z j hp I
    (SerreGlobal.Finite.output p k n X Y f i g D.codimension
      (tracePoint (g := g) p k n X Y f i s₀ hbase B hB))

abbrev nativeBelow := PrincipalSource.IntrinsicSupport.Intrinsic.punctured (f ≫ i).left U hU
  (Y.left.basicOpen z) (selectedOpen p k n X Y f i U hgood z).property
  (selectedBelow p k n X Y f i U hgood z) D.parameters (outside p k n Y s₀)
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_punctured
abbrev nativeCover := PrincipalSource.IntrinsicSupport.Intrinsic.cover (f ≫ i).left U hU
  (Y.left.basicOpen z) (selectedOpen p k n X Y f i U hgood z).property
  (selectedBelow p k n X Y f i U hgood z) D.parameters (outside p k n Y s₀)
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_cover
abbrev nativeGlobal := PrincipalSource.IntrinsicSupport.Intrinsic.global (f ≫ i).left U hU
  (Y.left.basicOpen z) (selectedOpen p k n X Y f i U hgood z).property
  (selectedBelow p k n X Y f i U hgood z) (outside p k n Y s₀)
  (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_global
abbrev residue := PrincipalFractionGlobal.boundedResidue p k n Y Z j hp
  (selectedOpen p k n X Y f i U hgood z) I g (FinitePointValueData.parameters p k n X Y f i s₀ U hU D hgood z)
  (outside p k n Y s₀) (nativeBelow p k n X Y f i s₀ hbase U hU D hgood z hz)
  (nativeCover p k n X Y f i s₀ hbase U hU D hgood z hz)
  (nativeGlobal p k n X Y f i s₀ hbase U hU D hgood z hz)

abbrev rawValue := by
  letI := FiniteEtale.SelectedSourceRecovery.targetClosed X Y f i s₀ hbase
  exact ProjectivePoint.ResidueSingleCoordinates.rawValue X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction (Truncated.Witt.Ring p k n) Y X f s₀ hbase)
    B hB U hU D

variable (r : WittVector p k)
  (hr : Truncated.Witt.quotient p k n r = rawValue p k n X Y f i s₀ hbase B hB U hU D)
  {κ : Type} [CommRing κ]
  (η : Γ(Y.left,(selectedOpen p k n X Y f i U hgood z).val) →+* κ)
  (hk : Koszul.OrientedTopCohomology.ideal Γ(Y.left,(selectedOpen p k n X Y f i U hgood z).val)
      (FinitePointValueData.parameters p k n X Y f i s₀ U hU D hgood z) = RingHom.ker η)
  (hzlocal : η (Y.left.presheaf.map (homOfLE (selectedBelow p k n X Y f i U hgood z)).op z) = 1)

include hk hzlocal hr in
abbrev native_input := by
  letI := FiniteEtale.SelectedSourceRecovery.targetClosed X Y f i s₀ hbase
  have heq := FiniteSelectedClass.native_eq p k n X Y f i s₀ hbase B hB U hU D z
    (selectedOpen p k n X Y f i U hgood z) (selectedBelow p k n X Y f i U hgood z)
  have hi := Projective.SelectedFraction.Coordinates.native_input p k n X i (s₀ ≫ f.left)
    (SectionEvaluationNaturality.image_retraction (Truncated.Witt.Ring p k n) Y X f s₀ hbase)
    B hB U hU D Y f Z j hp (selectedOpen p k n X Y f i U hgood z)
    (selectedBelow p k n X Y f i U hgood z) z r hr η hk hzlocal
  have h := congrArg (fun x => ModelPrincipalSheaf.input p k n Y
    (Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) (f ≫ i) U
    (selectedOpen p k n X Y f i U hgood z) (selectedBelow p k n X Y f i U hgood z) g D.codimension D.parameters
    (ULift.up.{2,1} (ULift.up.{1,0} x))) heq
  exact h.trans hi

include hk hzlocal hr in
omit [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [GeometricallyConnected Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem local_fraction :
    evaluate p k n X Y f i s₀ U hU D Z j hp I
      (nativeMap p k n X Y f i s₀ hbase U hU D hgood z hz
        (nativeClass p k n X Y f i s₀ hbase B hB U hU D hgood z)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
        ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
          residue p k n X Y f i s₀ hbase U hU D hgood z hz Z j hp I)) := by
  let := D.finiteVariables
  let : LinearOrder D.coordinateIndex :=
    LinearOrder.lift' (Fintype.equivFin D.coordinateIndex) (Fintype.equivFin D.coordinateIndex).injective
  let := Projective.ParameterOpenEtale.sourceAlgebra X i (s₀ ≫ f.left) g U hU D.toParameterData Y f
    (Y.left.basicOpen z) (selectedBelow p k n X Y f i U hgood z)
  let := Projective.ParameterOpenEtale.sourceTower X i (s₀ ≫ f.left) g U hU D.toParameterData Y f
    (Y.left.basicOpen z) (selectedBelow p k n X Y f i U hgood z)
  let := Projective.ParameterOpenEtale.sourceEtale X i (s₀ ≫ f.left) g U hU D.toParameterData Y f
    (Y.left.basicOpen z) (selectedOpen p k n X Y f i U hgood z).property
    (selectedBelow p k n X Y f i U hgood z)
  have hi := native_input p k n X Y f i s₀ hbase B hB U hU D hgood z Z j hp r hr η hk hzlocal
  have h := TransportedPrincipalFraction.fraction p k n Y Z j hp I
    (f ≫ i).left U hU (selectedOpen p k n X Y f i U hgood z) (selectedBelow p k n X Y f i U hgood z)
    g D.parameters (outside p k n Y s₀) (cover p k n X Y f i) (coverFull p k n X Y f i)
    (coverAffine p k n X Y f i)
    (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_affine
    (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_punctured
    (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_cover
    (conditions p k n X Y f i s₀ hbase U hU D hgood z hz).selected.wide_global
    D.coordinateIndex D.codimension (nativeClass p k n X Y f i s₀ hbase B hB U hU D hgood z)
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g) r hi
  convert h using 1
  as_aux_lemma => rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValueData
