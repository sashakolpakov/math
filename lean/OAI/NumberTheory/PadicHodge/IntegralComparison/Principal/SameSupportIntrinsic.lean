import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSameSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions

/-! # Same Support Intrinsic -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SameSupportIntrinsic.Intrinsic

noncomputable section

/-! Restricting to any affine neighborhood of the same support gives
the literal native principal comparison for every original class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover

variable {Y Z : Scheme.{0}} [Y.IsSeparated] (π : Y ⟶ Z) [IsAffineHom π]
  (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
  (hVU : V ≤ π ⁻¹ᵁ U) {g : ℕ} (t : Fin g → Γ(Z,U))
  (O : Y.Opens)
  (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions (PrincipalSource.OpenReindex.wideOpens π U hU)
    (PrincipalSource.OpenReindex.geometricOpens π U hU V) (PrincipalPoint.Fraction.family U t) O O)
  (N : Y.Modules) [N.IsQuasicoherent] (c q : ℕ)
  {μ : Type} [LinearOrder μ] (A : μ → Y.Opens)
  (hA : iSup A = ⊤) (haA : ∀ j, IsAffineOpen (A j))

private abbrev family := PrincipalPoint.Fraction.family U t
private abbrev geometric := PrincipalSource.OpenReindex.geometricOpens π U hU V
private abbrev nativeFamily := (PrincipalSource.OpenReindex.reindex π U V hVU).obj ∘ family U t
private abbrev single := Affine.OrderedInjective.Comparison.sourcePresheaf N c

local instance native_tuples : ∀ (d : ℕ) (a : Fin (d+1) → ULift (Fin g)),
    PreservesLimit (Discrete.functor (nativeFamily π U V hVU t ∘ a))
      (AdditiveSections.opens V hV) :=
  fun _ a => AffinePrincipal.Products.preserves Y V hV (nativeFamily π U V hVU t ∘ a)

def nativeComparison :
    (AffinePrincipal.Injective.Comparison.source (AdditiveSections.opens V hV)
      (nativeFamily π U V hVU t) N c).homology q ⟶
    (Affine.OrderedInjective.Comparison.source N c A).homology q := by
  letI := CanonicalRefinement.relative_source (geometric π U hU V)
    (family U t) O H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover N c q
  letI := CanonicalRefinement.ordered_source (geometric π U hU V)
    O H.selected.wide_affine H.selected.wide_global A hA haA N c q
  letI := PrincipalSource.Intrinsic.IntrinsicComparison.native_isIso π U hU V hV hVU
    (single N c) (CanonicalCover.complementary O) (CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (CanonicalCover.localRight (geometric π U hU V) (family U t) O) q
  exact PresheafCover.Comparison.comparison (AdditiveSections.opens V hV)
    (nativeFamily π U V hVU t) (CanonicalCover.complementary O)
    (CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (PrincipalSource.Intrinsic.IntrinsicComparison.localRefinement π U hU V hV hVU t
      (CanonicalCover.localCover (geometric π U hU V) (family U t) O)
      (CanonicalCover.localLeft (geometric π U hU V) (family U t) O))
    (CanonicalCover.localRight (geometric π U hU V) (family U t) O)
    A (CanonicalCover.globalCover (geometric π U hU V) O A)
    (PrincipalSource.Intrinsic.IntrinsicComparison.globalRefinement π U hU V hV hVU
      (CanonicalCover.complementary O) (CanonicalCover.globalCover (geometric π U hU V) O A)
      (CanonicalCover.globalLeft (geometric π U hU V) O A))
    (CanonicalCover.globalRight (geometric π U hU V) O A) (single N c) q

omit [IsAffineHom π] in
theorem reindex_comparison :
    homologyMap (PrincipalSource.Intrinsic.IntrinsicComparison.sourceIso π U hU V hV hVU t
      (single N c)).hom q ≫ nativeComparison π U hU V hV hVU t O H N c q A hA haA =
    CanonicalSupportCover.comparison (geometric π U hU V) (family U t)
      O H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover
      H.selected.wide_global N c A hA haA q := by
  let := CanonicalRefinement.relative_source (geometric π U hU V)
    (family U t) O H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover N c q
  let := CanonicalRefinement.ordered_source (geometric π U hU V)
    O H.selected.wide_affine H.selected.wide_global A hA haA N c q
  exact PrincipalSource.Intrinsic.IntrinsicComparison.comparison π U hU V hV hVU t (single N c)
    (CanonicalCover.complementary O) (CanonicalCover.localCover (geometric π U hU V) (family U t) O)
    (CanonicalCover.localLeft (geometric π U hU V) (family U t) O)
    (CanonicalCover.localRight (geometric π U hU V) (family U t) O)
    A (CanonicalCover.globalCover (geometric π U hU V) O A)
    (CanonicalCover.globalLeft (geometric π U hU V) O A) (CanonicalCover.globalRight (geometric π U hU V) O A) q

omit [IsAffineHom π] in
theorem comparison :
    CanonicalSupportCover.comparison (PrincipalSource.OpenReindex.wideOpens π U hU) (family U t)
      O H.wide_affine H.wide_punctured H.wide_cover H.wide_global N c A hA haA q =
    homologyMap (PrincipalSource.IntrinsicCoordinates.Intrinsic.sourceMap π U hU V hV hVU N t c) q ≫
      nativeComparison π U hU V hV hVU t O H N c q A hA haA := by
  have hs := SingleSameSupport.comparison (PrincipalSource.OpenReindex.wideOpens π U hU) (geometric π U hU V)
    (PrincipalSource.OpenReindex.geometricInclusion π U hU V) (family U t) O H N c q A hA haA
  rw [← reindex_comparison π U hU V hV hVU t O H N c q A hA haA] at hs
  simp only [PrincipalSource.IntrinsicCoordinates.Intrinsic.sourceMap, homologyMap_comp, Category.assoc]
  convert hs.symm using 1; rfl

omit [IsAffineHom π] in
theorem recovery (x : (AffinePrincipal.Injective.Comparison.source
    (PrincipalSource.OpenReindex.wideOpens π U hU) (family U t) N c).homology q) :
    CanonicalSupportCover.comparison (PrincipalSource.OpenReindex.wideOpens π U hU) (family U t)
      O H.wide_affine H.wide_punctured H.wide_cover H.wide_global N c A hA haA q x =
    nativeComparison π U hU V hV hVU t O H N c q A hA haA
      (homologyMap (PrincipalSource.IntrinsicCoordinates.Intrinsic.sourceMap π U hU V hV hVU N t c) q x) :=
  ConcreteCategory.congr_hom (comparison π U hU V hV hVU t O H N c q A hA haA) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SameSupportIntrinsic.Intrinsic
