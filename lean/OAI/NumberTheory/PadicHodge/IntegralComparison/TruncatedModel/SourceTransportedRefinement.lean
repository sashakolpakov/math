import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.TransportedRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CanonicalRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexCoefficientIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass

/-! # Source Transported Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTransportedRefinement

noncomputable section

/-! All original and native refinement isomorphisms on the transported
geometric covers used by the selected source comparison. The single
source degree is arbitrary, including both the original and top degrees. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  {Z : Scheme.{0}} (π : X.left ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)
  (V : X.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  {m : ℕ} (t : Fin m → Γ(Z,U)) (O : X.left.Opens)

variable (hF : ∀ r, IsAffineOpen ((PrincipalSource.OpenReindex.geometricOpens π U hU V).obj r))
  (hpunct : ∀ j, (PrincipalSource.OpenReindex.geometricOpens π U hU V).obj (PrincipalPoint.Fraction.family U t j) ≤ O)
  (hcover : (PrincipalSource.OpenReindex.geometricOpens π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊓ O ≤
    ⨆ j, (PrincipalSource.OpenReindex.geometricOpens π U hU V).obj (PrincipalPoint.Fraction.family U t j))
  (hglobal : (PrincipalSource.OpenReindex.geometricOpens π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊔ O = ⊤)
  {μ : Type} [LinearOrder μ] (A : μ → X.left.Opens)
  (hA : iSup A = ⊤) (haA : ∀ j, IsAffineOpen (A j))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (c q : ℕ)

abbrev form := TopCover.form p k n X g
abbrev original := Affine.OrderedInjective.Comparison.sourcePresheaf (form p k n X g) c
abbrev moduleSource := Relative.AdditiveCechConcentration.coefficients
  ((single X.left.Modules (.up ℕ) c).obj (form p k n X g))
abbrev source := ((TopCover.coefficients p k n X).mapHomologicalComplex
  (.up ℕ)).obj ((single X.left.Modules (.up ℕ) c).obj (form p k n X g))
abbrev linear := CechIso.ResolutionGlobal.presheaf p k n X Y f I
abbrev target := AdditiveTop.Comparison.target p k n X Y f I

def moduleSourceIso : original p k n X g c ≅ moduleSource p k n X g c :=
  (Principal.RelativeSupportedClass.singleCoefficientIso (form p k n X g) c).symm

include hVU hF hpunct hcover in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem relative_original : IsIso (RelativeCech.Refinement.homology
    ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) (original p k n X g c) q) := by
  let := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g
  exact PrincipalSource.TransportedRefinement.relative_source π U hU V hV hVU t O
    hF hpunct hcover (form p k n X g) c q

include hF hglobal hA haA in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem ordered_original : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
    (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
    (original p k n X g c)) q) := by
  let := IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g
  exact PrincipalSource.TransportedRefinement.ordered_source π U hU V O hF hglobal A hA haA
    (form p k n X g) c q

include hVU hF hpunct hcover in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem relative_source : IsIso (RelativeCech.Refinement.homology
    ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) (source p k n X g c) q) := by
  let := relative_original p k n X π U hU V hV hVU t O hF hpunct hcover g c q
  let : IsIso (RelativeCech.Refinement.homology
      ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) (moduleSource p k n X g c) q) :=
    Cech.ComplexCoefficientIso.relative
      (moduleSourceIso p k n X g c)
      ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
      (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
      (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) q
  exact Presheaf.CoverCoefficients.relative_isIso AdditiveTop.Comparison.lift
    (moduleSource p k n X g c) ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) q

include hF hglobal hA haA in
omit [Fintype k] [CharP k p] [SmoothOfRelativeDimension g X.hom] in
theorem ordered_source : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
    (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
    (source p k n X g c)) q) := by
  let := ordered_original p k n X π U hU V O hF hglobal A hA haA g c q
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
      (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
      (moduleSource p k n X g c)) q) :=
    Cech.ComplexCoefficientIso.ordered
      (moduleSourceIso p k n X g c)
      A (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) q
  exact Presheaf.CoverCoefficients.ordered_isIso AdditiveTop.Comparison.lift
    (moduleSource p k n X g c) A (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
    (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) q

include hVU hpunct hcover in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem relative_linear : IsIso (RelativeCech.Refinement.homology
    ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) (linear p k n X Y f I) q) := by
  let := CanonicalRefinement.relative p k n X Y f I
    (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O hpunct hcover q
  exact PrincipalSource.Intrinsic.IntrinsicComparison.native_isIso π U hU V hV hVU
    (linear p k n X Y f I) (Principal.CanonicalCover.complementary O)
    (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) q

include hglobal hA in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem ordered_linear : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
    (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
    (linear p k n X Y f I)) q) :=
  CanonicalRefinement.ordered p k n X Y f I
    (PrincipalSource.OpenReindex.geometricOpens π U hU V) O hglobal A hA q

include hVU hpunct hcover in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem relative_target : IsIso (RelativeCech.Refinement.homology
    ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) (target p k n X Y f I) q) := by
  let := relative_linear p k n X Y f I π U hU V hV hVU t O hpunct hcover q
  exact Presheaf.CoverCoefficients.relative_isIso (AdditiveTop.Comparison.forget p k)
    (linear p k n X Y f I) ((Principal.AdditiveSections.opens V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (Principal.CanonicalCover.complementary O) (Principal.CanonicalCover.localCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O)
    (Principal.CanonicalCover.localRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O) q

include hglobal hA in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem ordered_target : IsIso (homologyMap (OrderedCech.Refinement.totalMap A
    (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
    (target p k n X Y f I)) q) := by
  let := ordered_linear p k n X Y f I π U hU V O hglobal A hA q
  exact Presheaf.CoverCoefficients.ordered_isIso (AdditiveTop.Comparison.forget p k)
    (linear p k n X Y f I) A (Principal.CanonicalCover.globalCover (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A)
    (Principal.CanonicalCover.globalRight (PrincipalSource.OpenReindex.geometricOpens π U hU V) O A) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTransportedRefinement
