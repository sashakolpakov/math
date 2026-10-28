import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalData

/-! # Transported Principal Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalFraction

noncomputable section

/-! The signed bounded fraction formula on the literal transported
geometric covers, with every refinement isomorphism derived. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  {Z : Scheme.{0}} (π : X.left ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)
  (V : X.left.affineOpens) (hVU : V.val ≤ π ⁻¹ᵁ U)
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (t : Fin g → Γ(Z,U))
  (O : X.left.Opens)

variable {μ : Type} [LinearOrder μ] (A : μ → X.left.Opens)
  (hA : iSup A = ⊤) (haA : ∀ j, IsAffineOpen (A j))

variable
  (hF : ∀ r, IsAffineOpen ((TransportedPrincipalData.Fraction.geometric π U hU V).obj r))
  (hpunct : ∀ j, (TransportedPrincipalData.Fraction.geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j) ≤ O)
  (hcover : (TransportedPrincipalData.Fraction.geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊓ O ≤
    ⨆ j, (TransportedPrincipalData.Fraction.geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j))
  (hglobal : (TransportedPrincipalData.Fraction.geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊔ O = ⊤)

attribute [local instance] TransportedPrincipalData.Fraction.native_tuples

variable (τ : Type) [LinearOrder τ]
  [Algebra (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X V.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X V.val)]
  [Algebra.Etale (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X V.val)]
  (c : ℕ) (x : (TransportedPrincipalData.Fraction.originalSource p k n X π U V hVU g t c).homology (g+c))
  (d : ℤ) (b : WittVector p k)
  (hx : PrincipalSheafValue.input p k n X g c
    (TransportedPrincipalData.Fraction.native V) (TransportedPrincipalData.Fraction.family π U V hVU g t) (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    d • ModelPrincipalFraction.input p k n X Y f hp V g
      (TransportedPrincipalData.Fraction.parameters π U V hVU g t) c b)

include hF hpunct hcover hglobal hA haA τ in
abbrev fraction := by
  letI : IsIso (RelativeCech.Refinement.homology
      ((PrincipalSheafFraction.opens p k n X V).obj
        (⊤_ (PrincipalFrame.Index X.left V)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (PrincipalSheafFraction.original p k n X g c) (g+c)) :=
    TransportedPrincipalData.Fraction.original_relative p k n X π U hU V hVU g t O hF hpunct hcover c (g+c)
  letI : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (TransportedPrincipalData.Fraction.geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (TransportedPrincipalData.Fraction.geometric π U hU V) O A)
      (PrincipalSheafFraction.original p k n X g c)) (g+c)) :=
    TransportedPrincipalData.Fraction.original_ordered p k n X π U hU V g O A hA haA hF hglobal c (g+c)
  letI : IsIso (RelativeCech.Refinement.homology
      ((PrincipalSheafFraction.opens p k n X V).obj
        (⊤_ (PrincipalFrame.Index X.left V)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (PrincipalTopDegree.source p k n X g c) (g+c)) :=
    TransportedPrincipalData.Fraction.source_relative p k n X π U hU V hVU g t O hF hpunct hcover c (g+c)
  letI : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (TransportedPrincipalData.Fraction.geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (TransportedPrincipalData.Fraction.geometric π U hU V) O A)
      (PrincipalTopDegree.source p k n X g c)) (g+c)) :=
    TransportedPrincipalData.Fraction.source_ordered p k n X π U hU V g O A hA haA hF hglobal c (g+c)
  letI : IsIso (RelativeCech.Refinement.homology
      ((PrincipalSheafFraction.opens p k n X V).obj
        (⊤_ (PrincipalFrame.Index X.left V)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (PrincipalSheafFraction.source p k n X g) (g+g)) :=
    TransportedPrincipalData.Fraction.source_relative p k n X π U hU V hVU g t O hF hpunct hcover g (g+g)
  letI : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (TransportedPrincipalData.Fraction.geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (TransportedPrincipalData.Fraction.geometric π U hU V) O A)
      (PrincipalSheafFraction.source p k n X g)) (g+g)) :=
    TransportedPrincipalData.Fraction.source_ordered p k n X π U hU V g O A hA haA hF hglobal g (g+g)
  letI : IsIso (RelativeCech.Refinement.homology
      ((PrincipalSheafFraction.opens p k n X V).obj
        (⊤_ (PrincipalFrame.Index X.left V)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (PrincipalSheafFraction.linear p k n X Y f I) (g+g)) :=
    TransportedPrincipalData.Fraction.linear_relative p k n X Y f I π U hU V hVU g t O hpunct hcover (g+g)
  letI : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (TransportedPrincipalData.Fraction.geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (TransportedPrincipalData.Fraction.geometric π U hU V) O A)
      (PrincipalSheafFraction.linear p k n X Y f I)) (g+g)) :=
    TransportedPrincipalData.Fraction.linear_ordered p k n X Y f I π U hU V O A hA hglobal (g+g)
  exact PrincipalSheafFraction.fraction p k n X Y f hp V I g
    (TransportedPrincipalData.Fraction.parameters π U V hVU g t) (Principal.CanonicalCover.complementary O)
    (Principal.CanonicalCover.localCover (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (TransportedPrincipalData.Fraction.leftRefinement (p := p) (k := k) (n := n) (X := X) π U hU V hVU g t O)
    (Principal.CanonicalCover.localRight (TransportedPrincipalData.Fraction.geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
    A hA (Principal.CanonicalCover.globalCover (TransportedPrincipalData.Fraction.geometric π U hU V) O A) (TransportedPrincipalData.Fraction.globalRefinement (p := p) (k := k) (n := n) (X := X) π U hU V hVU O A)
    (Principal.CanonicalCover.globalRight (TransportedPrincipalData.Fraction.geometric π U hU V) O A) O
    (TransportedPrincipalData.Fraction.native_punctured (p := p) (k := k) (n := n) (X := X) π U hU V hVU g t O hpunct)
    (ComplementaryAffineCover.le O)
    (TransportedPrincipalData.Fraction.native_cover (p := p) (k := k) (n := n) (X := X) π U hU V hVU g t O hcover)
    (TransportedPrincipalData.Fraction.native_global (p := p) (k := k) (n := n) (X := X) π U hU V hVU O hglobal) c τ x d b hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalFraction
