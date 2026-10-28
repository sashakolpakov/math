import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.CanonicalCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicCoordinates

/-! # Intrinsic Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicRecovery.Intrinsic

noncomputable section

/-! Recovery on the selected native principal open through the actual
transported canonical complementary and common covers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalCover

private theorem recover {A B C D E : AddCommGrpCat}
    (r : A ⟶ B) (l : B ⟶ E) (a : A ⟶ C) (s : C ⟶ D) (n : D ⟶ E)
    (w : A ⟶ E) (x : A) (h : r ≫ l = a ≫ s ≫ n) (hx : w x = l (r x)) :
    w x = n (s (a x)) :=
  hx.trans (ConcreteCategory.congr_hom h x)

variable {Y X Z : Scheme.{0}} [Y.IsSeparated] (f : Y ⟶ X) (i : X ⟶ Z)
  [IsAffineHom (f ≫ i)] (U : Z.Opens) (hU : IsAffineOpen U)
  {g : ℕ} (t : Fin g → Γ(Z,U)) (N : Y.Modules) [N.IsQuasicoherent]
  (z : Γ(Y,(f ≫ i) ⁻¹ᵁ U)) (O₁ O₂ : Y.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (PrincipalPoint.Fraction.family U t) O₁ O₂)
  (hza : IsAffineOpen (Y.basicOpen z)) (hZU : Y.basicOpen z ≤ (f ≫ i) ⁻¹ᵁ U)
  (c n : ℕ) {μ : Type} [LinearOrder μ] (V : μ → Y.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))

private abbrev family := PrincipalPoint.Fraction.family U t
private abbrev geometric := OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)
private abbrev nativeFamily :=
  (OpenReindex.reindex (f ≫ i) U (Y.basicOpen z) hZU).obj ∘ family U t
private abbrev single := Affine.OrderedInjective.Comparison.sourcePresheaf N c
private abbrev forgetScalars : ModuleCat.{0} Γ(Z,U) ⥤ AddCommGrpCat := forget₂ _ _
private abbrev group := (OpenRestriction.supportedFunctor U (family U t) c (n+c)).obj
  (OpenFixedClass.source f i U hU N)

local instance native_tuples : ∀ (d : ℕ) (a : Fin (d+1) → ULift (Fin g)),
    PreservesLimit (Discrete.functor (nativeFamily f i U t z hZU ∘ a)) (Principal.AdditiveSections.opens (Y.basicOpen z) hza) :=
  fun _ a => AffinePrincipal.Products.preserves Y (Y.basicOpen z) hza
    (nativeFamily f i U t z hZU ∘ a)

def nativeComparison :
    (AffinePrincipal.Injective.Comparison.source (Principal.AdditiveSections.opens (Y.basicOpen z) hza)
      (nativeFamily f i U t z hZU) N c).homology (n+c) ⟶
    (Affine.OrderedInjective.Comparison.source N c V).homology (n+c) := by
  letI := Principal.CanonicalRefinement.relative_source (geometric f i U hU z)
    (family U t) O₂ H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover N c (n+c)
  letI := Principal.CanonicalRefinement.ordered_source (geometric f i U hU z)
    O₂ H.selected.wide_affine H.selected.wide_global V hV haV N c (n+c)
  letI := Intrinsic.IntrinsicComparison.native_isIso (f ≫ i) U hU (Y.basicOpen z) hza hZU
    (single N c) (Principal.CanonicalCover.complementary O₂) (Principal.CanonicalCover.localCover (geometric f i U hU z) (family U t) O₂)
    (Principal.CanonicalCover.localRight (geometric f i U hU z) (family U t) O₂) (n+c)
  exact Principal.PresheafCover.Comparison.comparison (Principal.AdditiveSections.opens (Y.basicOpen z) hza)
    (nativeFamily f i U t z hZU) (Principal.CanonicalCover.complementary O₂)
    (Principal.CanonicalCover.localCover (geometric f i U hU z) (family U t) O₂)
    (Intrinsic.IntrinsicComparison.localRefinement (f ≫ i) U hU (Y.basicOpen z) hza hZU t
      (Principal.CanonicalCover.localCover (geometric f i U hU z) (family U t) O₂)
      (Principal.CanonicalCover.localLeft (geometric f i U hU z) (family U t) O₂))
    (Principal.CanonicalCover.localRight (geometric f i U hU z) (family U t) O₂)
    V (Principal.CanonicalCover.globalCover (geometric f i U hU z) O₂ V)
    (Intrinsic.IntrinsicComparison.globalRefinement (f ≫ i) U hU (Y.basicOpen z) hza hZU
      (Principal.CanonicalCover.complementary O₂) (Principal.CanonicalCover.globalCover (geometric f i U hU z) O₂ V)
      (Principal.CanonicalCover.globalLeft (geometric f i U hU z) O₂ V))
    (Principal.CanonicalCover.globalRight (geometric f i U hU z) O₂ V) (single N c) (n+c)

omit [IsAffineHom (f ≫ i)] in
theorem comparison :
    homologyMap (Intrinsic.IntrinsicComparison.sourceIso (f ≫ i) U hU
      (Y.basicOpen z) hza hZU t (single N c)).hom (n+c) ≫
      nativeComparison f i U hU t N z O₁ O₂ H hza hZU c n V hV haV =
    Principal.CanonicalSupportCover.comparison (geometric f i U hU z) (family U t)
      O₂ H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover
      H.selected.wide_global N c V hV haV (n+c) := by
  let := Principal.CanonicalRefinement.relative_source (geometric f i U hU z)
    (family U t) O₂ H.selected.wide_affine H.selected.wide_punctured H.selected.wide_cover N c (n+c)
  let := Principal.CanonicalRefinement.ordered_source (geometric f i U hU z)
    O₂ H.selected.wide_affine H.selected.wide_global V hV haV N c (n+c)
  exact Intrinsic.IntrinsicComparison.comparison (f ≫ i) U hU (Y.basicOpen z) hza hZU t
    (single N c) (Principal.CanonicalCover.complementary O₂) (Principal.CanonicalCover.localCover (geometric f i U hU z) (family U t) O₂)
    (Principal.CanonicalCover.localLeft (geometric f i U hU z) (family U t) O₂)
    (Principal.CanonicalCover.localRight (geometric f i U hU z) (family U t) O₂)
    V (Principal.CanonicalCover.globalCover (geometric f i U hU z) O₂ V)
    (Principal.CanonicalCover.globalLeft (geometric f i U hU z) O₂ V) (Principal.CanonicalCover.globalRight (geometric f i U hU z) O₂ V) (n+c)

omit [IsAffineHom (f ≫ i)] in
theorem restriction_comparison :
    (forgetScalars U).map (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c)) ≫
      CanonicalCover.localComparison f i U hU t N z O₁ O₂ H c n V hV haV =
    (SupportedCoordinates.wideIso f i U hU (family U t) N c (n+c)).hom ≫
      homologyMap (IntrinsicCoordinates.Intrinsic.sourceMap (f ≫ i) U hU
        (Y.basicOpen z) hza hZU N t c) (n+c) ≫
      nativeComparison f i U hU t N z O₁ O₂ H hza hZU c n V hV haV := by
  dsimp only [CanonicalCover.localComparison]
  rw [← comparison f i U hU t N z O₁ O₂ H hza hZU c n V hV haV]
  simp only [← Category.assoc]
  rw [SupportedCoordinates.restriction_square]
  simp only [IntrinsicCoordinates.Intrinsic.sourceMap, homologyMap_comp, Category.assoc]
  rfl

theorem recovery (x : group f i U hU t N c n)
    (hx : (OpenRestriction.supportedFunctor U (family U t) c (n+c)).map
      (OpenFixedClass.scalar f i U hU N z) x = x) :
    CanonicalCover.wideComparison f i U hU t N z O₁ O₂ H c n V hV haV x =
    nativeComparison f i U hU t N z O₁ O₂ H hza hZU c n V hV haV
      (homologyMap (IntrinsicCoordinates.Intrinsic.sourceMap (f ≫ i) U hU
        (Y.basicOpen z) hza hZU N t c) (n+c)
        ((SupportedCoordinates.wideIso f i U hU (family U t) N c (n+c)).hom x)) := by
  exact recover
    ((forgetScalars U).map (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c)))
    (CanonicalCover.localComparison f i U hU t N z O₁ O₂ H c n V hV haV)
    (SupportedCoordinates.wideIso f i U hU (family U t) N c (n+c)).hom
    (homologyMap (IntrinsicCoordinates.Intrinsic.sourceMap (f ≫ i) U hU
      (Y.basicOpen z) hza hZU N t c) (n+c))
    (nativeComparison f i U hU t N z O₁ O₂ H hza hZU c n V hV haV)
    (CanonicalCover.wideComparison f i U hU t N z O₁ O₂ H c n V hV haV)
    x (restriction_comparison f i U hU t N z O₁ O₂ H hza hZU c n V hV haV)
    (CanonicalCover.recovery f i U hU t N z O₁ O₂ H c n V hV haV x hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicRecovery.Intrinsic
