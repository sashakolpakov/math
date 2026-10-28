import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover

/-! # Canonical Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.CanonicalCover

noncomputable section

/-! Canonical affine cover recovery for the original finite-source class.
The geometric support conditions derive every refinement isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem after_candidate {A B C : AddCommGrpCat}
    (s : B ⟶ A) (f : A ⟶ C) (g : B ⟶ C) (h : s ≫ f = g)
    (x : A) (y : B) (hx : x = s y) : f x = g y := by
  rw [hx]
  exact ConcreteCategory.congr_hom h y

open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
variable {Y X Z : Scheme.{0}} [Y.IsSeparated] (f : Y ⟶ X) (i : X ⟶ Z)
  [IsAffineHom (f ≫ i)] (U : Z.Opens) (hU : IsAffineOpen U)
  {g : ℕ} (t : Fin g → Γ(Z,U)) (N : Y.Modules) [N.IsQuasicoherent]
  (z : Γ(Y,(f ≫ i) ⁻¹ᵁ U)) (O₁ O₂ : Y.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (PrincipalPoint.Fraction.family U t) O₁ O₂)
  (c n : ℕ) {μ : Type} [LinearOrder μ] (V : μ → Y.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))

private abbrev family := PrincipalPoint.Fraction.family U t
private abbrev forgetScalars : ModuleCat.{0} Γ(Z,U) ⥤ AddCommGrpCat := forget₂ _ _
private abbrev group := (OpenRestriction.supportedFunctor U (family U t) c (n+c)).obj
  (OpenFixedClass.source f i U hU N)

def wideComparison :
    (forgetScalars U).obj (group f i U hU t N c n) ⟶
      (Affine.OrderedInjective.Comparison.source N c V).homology (n+c) :=
  (SupportedCoordinates.wideIso f i U hU (family U t) N c (n+c)).hom ≫
    Principal.CanonicalSupportCover.comparison (OpenReindex.wideOpens (f ≫ i) U hU)
      (family U t) O₁ H.wide_affine H.wide_punctured H.wide_cover H.wide_global
      N c V hV haV (n+c)

def localComparison :
    (forgetScalars U).obj (group f i U hU t (OpenRestriction.extension (Y.basicOpen z) N) c n) ⟶
      (Affine.OrderedInjective.Comparison.source N c V).homology (n+c) :=
  (SupportedCoordinates.localIso
    f i U hU (family U t) N c (n+c) (Y.basicOpen z)).hom ≫
    Principal.CanonicalSupportCover.comparison (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
      (family U t) O₂ H.selected.wide_affine H.selected.wide_punctured
      H.selected.wide_cover H.selected.wide_global N c V hV haV (n+c)

omit [IsAffineHom (f ≫ i)] in
theorem candidate_comparison :
    SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c (n+c) ≫
      wideComparison f i U hU t N z O₁ O₂ H c n V hV haV =
    localComparison f i U hU t N z O₁ O₂ H c n V hV haV := by
  have h := Principal.CanonicalSupportCover.candidate_comparison
    (F := OpenReindex.wideOpens (f ≫ i) U hU) (W := family U t) (O := O₁)
    (N := N) (c := c) (V := V) (hV := hV) (haV := haV) (q := n+c)
    (G := OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)) (P := O₂) (H := H)
  simpa only [SupportedCandidate.candidate, wideComparison, localComparison,
    Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun a => (SupportedCoordinates.localIso
      f i U hU (family U t) N c (n+c) (Y.basicOpen z)).hom ≫ a) h

theorem recovery (x : group f i U hU t N c n)
    (hx : (OpenRestriction.supportedFunctor U (family U t) c (n+c)).map
      (OpenFixedClass.scalar f i U hU N z) x = x) :
    wideComparison f i U hU t N z O₁ O₂ H c n V hV haV x =
      localComparison f i U hU t N z O₁ O₂ H c n V hV haV
        (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x) :=
  after_candidate (SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c (n+c))
    (wideComparison f i U hU t N z O₁ O₂ H c n V hV haV)
    (localComparison f i U hU t N z O₁ O₂ H c n V hV haV)
    (candidate_comparison f i U hU t N z O₁ O₂ H c n V hV haV) x
    (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x)
    (SupportedCandidate.recovery f i U hU t N z O₁ O₂ H c n x hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.CanonicalCover
