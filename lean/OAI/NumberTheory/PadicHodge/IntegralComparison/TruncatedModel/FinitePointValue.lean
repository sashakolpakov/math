import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValueData

/-! # Finite Point Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValue

noncomputable section

/-! The original finite point class has its signed bounded residue
value through the selected component and the actual Serre maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite _root_.HomologicalComplex
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join_equalities {A : Type*} {a b c d : A}
    (hab : a = b) (hcd : c = d) (hbc : b = c) : a = d :=
  hab.trans (hbc.trans hcd)

private theorem lift_square_postcompose {A B C : AddCommGrpCat.{0}}
    {T S : AddCommGrpCat.{2}} (a : A ⟶ B) (c : A ⟶ C)
    (b : AdditiveTop.Comparison.lift.obj B ⟶ T)
    (d : AdditiveTop.Comparison.lift.obj C ⟶ T) (e : T ⟶ S)
    (h : AdditiveTop.Comparison.lift.map a ≫ b =
      AdditiveTop.Comparison.lift.map c ≫ d) (x : A) :
    e (b (ULift.up.{2,1} (ULift.up.{1,0} (a x)))) =
      e (d (ULift.up.{2,1} (ULift.up.{1,0} (c x)))) :=
  congrArg e (ConcreteCategory.congr_hom h (ULift.up.{2,1} (ULift.up.{1,0} x)))

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

variable (r : WittVector p k)
  (hr : Truncated.Witt.quotient p k n r = FinitePointValueData.rawValue p k n X Y f i s₀ hbase B hB U hU D)
  {κ : Type} [CommRing κ]
  (η : Γ(Y.left,(FinitePointValueData.selectedOpen p k n X Y f i U hgood z).val) →+* κ)
  (hk : Koszul.OrientedTopCohomology.ideal Γ(Y.left,(FinitePointValueData.selectedOpen p k n X Y f i U hgood z).val)
      (FinitePointValueData.parameters p k n X Y f i s₀ U hU D hgood z) = RingHom.ker η)
  (hzlocal : η (Y.left.presheaf.map (homOfLE (FinitePointValueData.selectedBelow p k n X Y f i U hgood z)).op z) = 1)

abbrev global_coordinate := lift_square_postcompose
  (SerreGlobal.Finite.output p k n X Y f i g D.codimension)
  (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g).inv
  (PrincipalSheafValue.globalValue p k n Y Z j hp I g D.codimension
    (FinitePointValueData.cover p k n X Y f i) (FinitePointValueData.coverFull p k n X Y f i))
  (ModelTopCoverComparison.globalInput p k n Y Z j hp I g
    (FinitePointValueData.cover p k n X Y f i) (FinitePointValueData.coverFull p k n X Y f i))
  (AdditiveGlobal.globalHomologyIso p k n Y Z j I (g+g)).hom
  (SerreGlobal.Finite.comparison p k n X Y f i Z j hp I g D.codimension)
  (FinitePointValueData.tracePoint (g := g) p k n X Y f i s₀ hbase B hB)

attribute [local irreducible] HomologicalComplex.homology

include he hk hzlocal hr in
omit [GeometricallyConnected X.hom] in
theorem fraction : FinitePointValueData.pointValue p k n X Y f i s₀ hbase B hB U hU D Z j hp I =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
        ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
          FinitePointValueData.residue p k n X Y f i s₀ hbase U hU D hgood z hz Z j hp I)) := by
  have hm := ConcreteCategory.congr_hom (FinitePointValueData.output_map p k n X Y f i s₀ U hU D)
    (FinitePointValueData.tracePoint (g := g) p k n X Y f i s₀ hbase B hB)
  have hn := FinitePointValueData.native_recovery p k n X Y f i s₀ hbase B hB U hU D hgood z hz he
  have hi := join_equalities hm hn (by as_aux_lemma => rfl)
  have h := congrArg (FinitePointValueData.evaluate p k n X Y f i s₀ U hU D Z j hp I) hi
  exact h.trans (FinitePointValueData.local_fraction p k n X Y f i s₀ hbase B hB U hU D hgood z hz Z j hp I r hr η hk hzlocal)

include he hk hzlocal hr in
abbrev global_fraction := by
  have hc := global_coordinate p k n X Y f i s₀ hbase B hB U hU D Z j hp I
  have hf := fraction p k n X Y f i s₀ hbase B hB U hU D hgood z hz he Z j hp I r hr η hk hzlocal
  exact join_equalities hc.symm hf (by as_aux_lemma => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValue
