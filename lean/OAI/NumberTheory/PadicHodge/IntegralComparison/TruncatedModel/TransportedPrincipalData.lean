import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTransportedRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction

/-! # Transported Principal Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalData.Fraction

noncomputable section

/-! The signed bounded fraction formula on the literal transported
geometric covers, with every refinement isomorphism derived. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover

abbrev parameters {Y Z : Scheme.{0}} (π : Y ⟶ Z) (U : Z.Opens)
    (V : Y.affineOpens) (hVU : V.val ≤ π ⁻¹ᵁ U) (g : ℕ) (t : Fin g → Γ(Z,U)) :=
  PrincipalResidue.ResidueRestriction.parameters π U V.val hVU t
abbrev geometric {Y Z : Scheme.{0}} (π : Y ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)
    (V : Y.affineOpens) := PrincipalSource.OpenReindex.geometricOpens π U hU V.val
abbrev native {Y : Scheme.{0}} (V : Y.affineOpens) :=
  Principal.AdditiveSections.opens V.val V.property
abbrev family {Y Z : Scheme.{0}} (π : Y ⟶ Z) (U : Z.Opens)
    (V : Y.affineOpens) (hVU : V.val ≤ π ⁻¹ᵁ U) (g : ℕ) (t : Fin g → Γ(Z,U)) :=
  PrincipalPoint.Fraction.family V.val (parameters π U V hVU g t)

local instance native_tuples {Y Z : Scheme.{0}} (π : Y ⟶ Z) (U : Z.Opens)
    (V : Y.affineOpens) (hVU : V.val ≤ π ⁻¹ᵁ U) (g : ℕ) (t : Fin g → Γ(Z,U))
    (d : ℕ) (a : Fin (d+1) → ULift (Fin g)) :
    PreservesLimit (Discrete.functor (family π U V hVU g t ∘ a)) (native V) :=
  AffinePrincipal.Products.preserves Y V.val V.property (family π U V hVU g t ∘ a)

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

abbrev original (c : ℕ) := PrincipalSheafValue.original p k n X g c
abbrev originalSource (c : ℕ) := AffinePrincipal.Injective.Comparison.source
  (native V) (family π U V hVU g t) (TopCover.form p k n X g) c

def leftRefinement := PrincipalSource.Intrinsic.IntrinsicComparison.localRefinement
  π U hU V.val V.property hVU t
  (Principal.CanonicalCover.localCover (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
  (Principal.CanonicalCover.localLeft (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)

variable {μ : Type} [LinearOrder μ] (A : μ → X.left.Opens)
  (hA : iSup A = ⊤) (haA : ∀ j, IsAffineOpen (A j))

def globalRefinement := PrincipalSource.Intrinsic.IntrinsicComparison.globalRefinement
  π U hU V.val V.property hVU (Principal.CanonicalCover.complementary O)
  (Principal.CanonicalCover.globalCover (geometric π U hU V) O A)
  (Principal.CanonicalCover.globalLeft (geometric π U hU V) O A)

variable
  (hF : ∀ r, IsAffineOpen ((geometric π U hU V).obj r))
  (hpunct : ∀ j, (geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j) ≤ O)
  (hcover : (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊓ O ≤
    ⨆ j, (geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j))
  (hglobal : (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊔ O = ⊤)

abbrev native_punctured := PrincipalSource.IntrinsicSupport.Intrinsic.punctured π U hU V.val V.property hVU t O hpunct
abbrev native_cover := PrincipalSource.IntrinsicSupport.Intrinsic.cover π U hU V.val V.property hVU t O hcover
abbrev native_global := PrincipalSource.IntrinsicSupport.Intrinsic.global π U hU V.val V.property hVU O hglobal

include hVU hF hpunct hcover in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem original_relative (c q : ℕ) :
    IsIso (RelativeCech.Refinement.homology
      ((native V).obj (⊤_ (Principal.SectionPresheaf.Index V.val)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (original p k n X g c) q) :=
  SourceTransportedRefinement.relative_original p k n X π U hU V.val V.property hVU t O
    hF hpunct hcover g c q

include hF hglobal hA haA in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem original_ordered (c q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (geometric π U hU V) O A)
      (original p k n X g c)) q) :=
  SourceTransportedRefinement.ordered_original p k n X π U hU V.val O
    hF hglobal A hA haA g c q

include hVU hF hpunct hcover in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem source_relative (c q : ℕ) :
    IsIso (RelativeCech.Refinement.homology
      ((native V).obj (⊤_ (Principal.SectionPresheaf.Index V.val)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (PrincipalTopDegree.source p k n X g c) q) :=
  SourceTransportedRefinement.relative_source p k n X π U hU V.val V.property hVU t O
    hF hpunct hcover g c q

include hF hglobal hA haA in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem source_ordered (c q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (geometric π U hU V) O A)
      (PrincipalTopDegree.source p k n X g c)) q) :=
  SourceTransportedRefinement.ordered_source p k n X π U hU V.val O
    hF hglobal A hA haA g c q

include hVU hpunct hcover in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem linear_relative (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology
      ((native V).obj (⊤_ (Principal.SectionPresheaf.Index V.val)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (CechIso.ResolutionGlobal.presheaf p k n X Y f I) q) :=
  SourceTransportedRefinement.relative_linear p k n X Y f I π U hU V.val V.property hVU t O
    hpunct hcover q

include hglobal hA in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem linear_ordered (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (Principal.CanonicalCover.globalRight (geometric π U hU V) O A)
      (CechIso.ResolutionGlobal.presheaf p k n X Y f I)) q) :=
  SourceTransportedRefinement.ordered_linear p k n X Y f I π U hU V.val O
    hglobal A hA q

include hF hpunct hcover hglobal hA haA in
def nativeComparison (c : ℕ) := by
  letI := original_relative p k n X π U hU V hVU g t O hF hpunct hcover c (g+c)
  letI := original_ordered p k n X π U hU V g O A hA haA hF hglobal c (g+c)
  exact Principal.PresheafCover.Comparison.comparison
    (native V) (family π U V hVU g t) (Principal.CanonicalCover.complementary O)
    (Principal.CanonicalCover.localCover (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (leftRefinement (p := p) (k := k) (n := n) (X := X) π U hU V hVU g t O)
    (Principal.CanonicalCover.localRight (geometric π U hU V) (PrincipalPoint.Fraction.family U t) O)
    A (Principal.CanonicalCover.globalCover (geometric π U hU V) O A) (globalRefinement (p := p) (k := k) (n := n) (X := X) π U hU V hVU O A)
    (Principal.CanonicalCover.globalRight (geometric π U hU V) O A) (original p k n X g c) (g+c)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TransportedPrincipalData.Fraction
