import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValueData

/-! # Smooth Point Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValue

noncomputable section

/-! The original smooth point class has its signed bounded residue
value, through the actual global and Serre comparison maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
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

variable (r : WittVector p k)
  (hr : Truncated.Witt.quotient p k n r =
    Projective.FormFraction.rawValue p k n X i s₀ hbase B hB U hU D)

abbrev global_coordinate := lift_square_postcompose
  (SerreGlobal.Smooth.output p k n X i g D.codimension)
  (Intrinsic.TopFormTrace.serreIso X i g).inv
  (PrincipalSheafValue.globalValue p k n X Y f hp I g D.codimension
    (SmoothPointValueData.cover p k n X i) (SmoothPointValueData.coverFull p k n X i))
  (ModelTopCoverComparison.globalInput p k n X Y f hp I g
    (SmoothPointValueData.cover p k n X i) (SmoothPointValueData.coverFull p k n X i))
  (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom
  (SerreGlobal.Smooth.comparison p k n X i Y f hp I g D.codimension)
  (SmoothPointValueData.tracePoint (g := g) p k n X i s₀ hbase B hB)

attribute [local irreducible] HomologicalComplex.homology

include hr in
theorem fraction : SmoothPointValueData.pointValue p k n X i s₀ hbase B hB U hU D Y f hp I =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension g •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
        ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
          SmoothPointValueData.residue p k n X i s₀ U hU D Y f hp I V hVU hcontains)) := by
  have hm := ConcreteCategory.congr_hom (SmoothPointValueData.output_map p k n X i s₀ U hU D)
    (SmoothPointValueData.tracePoint (g := g) p k n X i s₀ hbase B hB)
  have hn := SmoothPointValueData.native_recovery p k n X i s₀ hbase B hB U hU D V hVU hcontains
  have hi := join_equalities hm hn (by as_aux_lemma => rfl)
  have h := congrArg (SmoothPointValueData.evaluate p k n X i s₀ U hU D Y f hp I) hi
  exact h.trans (SmoothPointValueData.local_fraction p k n X i s₀ hbase B hB U hU D Y f hp I V hVU hcontains r hr)

include hr in
abbrev global_fraction := by
  have hc := global_coordinate p k n X i s₀ hbase B hB U hU D Y f hp I
  have hf := fraction p k n X i s₀ hbase B hB U hU D Y f hp I V hVU hcontains r hr
  exact join_equalities hc.symm hf (by as_aux_lemma => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValue
