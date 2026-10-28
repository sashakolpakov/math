import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectivePointSourceRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterOpenEtale
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SerreGlobal

/-! # Smooth Point Value Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValueData

noncomputable section

/-! The original smooth point class has the signed local residue value
on every affine neighborhood containing its section. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
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
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) [IsClosedImmersion i.left]
  (s₀ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X.left) [IsClosedImmersion s₀]
  (hbase : s₀ ≫ X.hom = 𝟙 _) (B : ℕ) (hB : d+2 ≤ B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space (Truncated.Witt.Ring p k n) (d+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i s₀ g U hU)
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (V : X.left.affineOpens) (hVU : V.val ≤ i.left ⁻¹ᵁ U)
  (hcontains : ⊤ ≤ s₀ ⁻¹ᵁ V.val)

attribute [local instance] IntegralComparison.Smooth.ProjectivePointTransfer.sourceSeparated
  IntegralComparison.Smooth.ProjectiveSectionClassData.composite_smooth
  IntegralComparison.Smooth.ProjectiveFormTrace.composite_proper IntegralComparison.Smooth.ProjectiveFormTrace.composite_connected

abbrev cover := Intrinsic.TopFormTrace.cover X i
abbrev coverFull := Intrinsic.TopFormTrace.cover_top X i
abbrev coverAffine := Intrinsic.TopFormTrace.cover_affine X i
abbrev form := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g
abbrev outside := SectionIdealPuncturedCover.outside s₀.ker
abbrev conditions := PrincipalPoint.SupportConditions.ProjectiveParameter.conditions X i s₀ g U hU D.toParameterData
  V.val V.property hVU hcontains
abbrev nativeClass := Projective.FormSourceCoordinates.nativeClass X i s₀ hbase B hB U hU D
  V.val V.property hVU
abbrev parameters := TransportedPrincipalData.Fraction.parameters i.left U V hVU g D.parameters

abbrev nativeMap := TransportedPrincipalData.Fraction.nativeComparison p k n X i.left U hU
  V hVU g D.parameters (outside p k n X s₀) (cover p k n X i) (coverFull p k n X i)
  (coverAffine p k n X i) (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_affine
  (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_punctured
  (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_cover
  (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_global D.codimension

abbrev native_recovery := by
  have hr := IntegralComparison.Smooth.ProjectivePointSourceRecovery.native_recovery X i s₀ hbase B hB U hU D
    V.val V.property hVU hcontains
  have hm := IntrinsicCoordinates.IntrinsicComparison.same p k n X g U hU D.parameters D.codimension
    (cover p k n X i) (coverFull p k n X i) (coverAffine p k n X i) i.left V hVU
    (outside p k n X s₀) (conditions p k n X i s₀ U hU D V hVU hcontains)
  exact join_equalities hr
    (congrArg (fun a => a (nativeClass p k n X i s₀ hbase B hB U hU D V hVU)) hm)
    (by as_aux_lemma => rfl)

def tracePoint : IntegralComparison.Smooth.ProjectiveFormTrace.cohomology X i g :=
  IntegralComparison.Smooth.ProjectiveSectionClassData.sectionClass X i s₀ hbase B hB g

omit [Fintype k] [CharP k p] [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [SmoothOfRelativeDimension g X.hom] [IsClosedImmersion (Over.Hom.left i)] [IsClosedImmersion s₀] in
theorem output_map :
    SerreGlobal.Smooth.output p k n X i g D.codimension =
      IntegralComparison.Smooth.ProjectivePointSourceRecovery.sourceOutput X i s₀ U hU D := rfl

def evaluate (x : (Affine.OrderedInjective.Comparison.source (form (g := g) p k n X) D.codimension
    (cover p k n X i)).homology (g+D.codimension)) :
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y) n (g+g) :=
  PrincipalSheafFraction.value p k n X Y f hp I g D.codimension
    (cover p k n X i) (coverFull p k n X i) (ULift.up.{2,1} (ULift.up.{1,0} x))

def pointValue : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n (g+g) :=
  evaluate p k n X i s₀ U hU D Y f hp I
    (SerreGlobal.Smooth.output p k n X i g D.codimension
      (tracePoint (g := g) p k n X i s₀ hbase B hB))

abbrev nativeBelow := PrincipalSource.IntrinsicSupport.Intrinsic.punctured i.left U hU V.val V.property hVU
  D.parameters (outside p k n X s₀)
  (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_punctured
abbrev nativeCover := PrincipalSource.IntrinsicSupport.Intrinsic.cover i.left U hU V.val V.property hVU
  D.parameters (outside p k n X s₀)
  (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_cover
abbrev nativeGlobal := PrincipalSource.IntrinsicSupport.Intrinsic.global i.left U hU V.val V.property hVU
  (outside p k n X s₀) (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_global
abbrev residue := PrincipalFractionGlobal.boundedResidue p k n X Y f hp V I g
  (SmoothPointValueData.parameters p k n X i s₀ U hU D V hVU) (outside p k n X s₀)
  (nativeBelow p k n X i s₀ U hU D V hVU hcontains)
  (nativeCover p k n X i s₀ U hU D V hVU hcontains)
  (nativeGlobal p k n X i s₀ U hU D V hVU hcontains)

variable (r : WittVector p k)
  (hr : Truncated.Witt.quotient p k n r =
    Projective.FormFraction.rawValue p k n X i s₀ hbase B hB U hU D)

include hr in
omit [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [GeometricallyConnected X.hom] in
theorem local_fraction :
    evaluate p k n X i s₀ U hU D Y f hp I
      (nativeMap p k n X i s₀ U hU D V hVU hcontains
        (nativeClass p k n X i s₀ hbase B hB U hU D V hVU)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
        ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
          residue p k n X i s₀ U hU D Y f hp I V hVU hcontains)) := by
  let := D.finiteVariables
  let : LinearOrder D.coordinateIndex :=
    LinearOrder.lift' (Fintype.equivFin D.coordinateIndex) (Fintype.equivFin D.coordinateIndex).injective
  let := Projective.ParameterOpenEtale.openAlgebra X i s₀ g U hU D.toParameterData V.val hVU
  let := Projective.ParameterOpenEtale.openTower X i s₀ g U hU D.toParameterData V.val hVU
  let := Projective.ParameterOpenEtale.openEtale X i s₀ g U hU D.toParameterData V.val V.property hVU
  have hi := Projective.FormFraction.native_input p k n X i s₀ hbase B hB U hU D
    Y f hp V hVU r hr
  have h := TransportedPrincipalFraction.fraction p k n X Y f hp I
    i.left U hU V hVU g D.parameters (outside p k n X s₀)
    (cover p k n X i) (coverFull p k n X i) (coverAffine p k n X i)
    (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_affine
    (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_punctured
    (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_cover
    (conditions p k n X i s₀ U hU D V hVU hcontains).selected.wide_global
    D.coordinateIndex D.codimension (nativeClass p k n X i s₀ hbase B hB U hU D V hVU)
    (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g) r hi
  convert h using 1
  as_aux_lemma => rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValueData
