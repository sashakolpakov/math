import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCandidate
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSupportCover

/-! # Supported Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCover

noncomputable section

/-! The original nested-pushforward principal class and its selected
restriction have the same genuine global Cech image. The only source
coordinate changes are the actual wide and local coefficient isomorphisms. -/
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
  (c n : ℕ)
  {κ₁ ν₁ ρ₁ κ₂ ν₂ ρ₂ μ : Type}
  [LinearOrder κ₁] [LinearOrder ν₁] [LinearOrder ρ₁]
  [LinearOrder κ₂] [LinearOrder ν₂] [LinearOrder ρ₂] [LinearOrder μ]
  (B₁ : κ₁ → Y.Opens) (J₁ : ν₁ → Y.Opens)
  (r₁ : FormalCoproduct.mk ν₁ J₁ ⟶ FormalCoproduct.mk (ULift (Fin g))
    ((OpenReindex.wideOpens (f ≫ i) U hU).obj ∘ PrincipalPoint.Fraction.family U t))
  (s₁ : FormalCoproduct.mk ν₁ J₁ ⟶ FormalCoproduct.mk κ₁ B₁)
  (B₂ : κ₂ → Y.Opens) (J₂ : ν₂ → Y.Opens)
  (r₂ : FormalCoproduct.mk ν₂ J₂ ⟶ FormalCoproduct.mk (ULift (Fin g))
    ((OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)).obj ∘ PrincipalPoint.Fraction.family U t))
  (s₂ : FormalCoproduct.mk ν₂ J₂ ⟶ FormalCoproduct.mk κ₂ B₂)
  (V : μ → Y.Opens) (hV : ∀ j, IsAffineOpen (V j))
  (T₁ : ρ₁ → Y.Opens)
  (l₁ : FormalCoproduct.mk ρ₁ T₁ ⟶ FormalCoproduct.mk (WithBot κ₁)
    (RelativeCech.Intersections.cover ((OpenReindex.wideOpens (f ≫ i) U hU).obj (⊤_ _)) B₁))
  (t₁ : FormalCoproduct.mk ρ₁ T₁ ⟶ FormalCoproduct.mk μ V)
  (T₂ : ρ₂ → Y.Opens)
  (l₂ : FormalCoproduct.mk ρ₂ T₂ ⟶ FormalCoproduct.mk (WithBot κ₂)
    (RelativeCech.Intersections.cover
      ((OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)).obj (⊤_ _)) B₂))
  (t₂ : FormalCoproduct.mk ρ₂ T₂ ⟶ FormalCoproduct.mk μ V)
  (hB₁ : ∀ j, B₁ j ≤ O₁) (hB₂ : ∀ j, B₂ j ≤ O₂)
  [IsIso (RelativeCech.Refinement.homology ((OpenReindex.wideOpens (f ≫ i) U hU).obj (⊤_ _)) B₁ J₁ s₁
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (n+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₁ t₁
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) (n+c))]
  [IsIso (RelativeCech.Refinement.homology ((OpenReindex.wideOpens (f ≫ i) U hU).obj (⊤_ _)) B₁ J₁ s₁
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) (n+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₁ t₁
    (Affine.OrderedInjective.Comparison.integerPresheaf N c)) (n+c))]
  [IsIso (RelativeCech.Refinement.homology
    ((OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)).obj (⊤_ _)) B₂ J₂ s₂
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (n+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₂ t₂
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) (n+c))]
  [IsIso (RelativeCech.Refinement.homology
    ((OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)).obj (⊤_ _)) B₂ J₂ s₂
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) (n+c))]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₂ t₂
    (Affine.OrderedInjective.Comparison.integerPresheaf N c)) (n+c))]

private abbrev family := PrincipalPoint.Fraction.family U t
private abbrev forgetScalars : ModuleCat.{0} Γ(Z,U) ⥤ AddCommGrpCat := forget₂ _ _
private abbrev group := (OpenRestriction.supportedFunctor U (family U t) c (n+c)).obj
  (OpenFixedClass.source f i U hU N)

def wideComparison :
    (forgetScalars U).obj (group f i U hU t N c n) ⟶
      (Affine.OrderedInjective.Comparison.source N c V).homology (n+c) :=
  (SupportedCoordinates.wideIso f i U hU (family U t) N c (n+c)).hom ≫
    Principal.SingleSupportedCover.originalComparison (OpenReindex.wideOpens (f ≫ i) U hU)
      (family U t) N c B₁ J₁ r₁ s₁ V T₁ l₁ t₁ (n+c)

def localComparison :
    (forgetScalars U).obj (group f i U hU t (OpenRestriction.extension (Y.basicOpen z) N) c n) ⟶
      (Affine.OrderedInjective.Comparison.source N c V).homology (n+c) :=
  (SupportedCoordinates.localIso
    f i U hU (family U t) N c (n+c) (Y.basicOpen z)).hom ≫
    Principal.SingleSupportedCover.originalComparison
      (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
      (family U t) N c B₂ J₂ r₂ s₂ V T₂ l₂ t₂ (n+c)

include hV hB₁ hB₂ in
omit [IsAffineHom (f ≫ i)] in
theorem candidate_comparison :
    SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c (n+c) ≫
      wideComparison f i U hU t N c n B₁ J₁ r₁ s₁ V T₁ l₁ t₁ =
    localComparison f i U hU t N z c n B₂ J₂ r₂ s₂ V T₂ l₂ t₂ := by
  have h := Principal.SelectedSupportCover.comparison
    (OpenReindex.wideOpens (f ≫ i) U hU) (OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (family U t) O₁ O₂ H N c B₁ J₁ r₁ s₁ B₂ J₂ r₂ s₂ V hV T₁ l₁ t₁ T₂ l₂ t₂ hB₁ hB₂ (n+c)
  simpa only [SupportedCandidate.candidate, wideComparison, localComparison,
    Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun a => (SupportedCoordinates.localIso
      f i U hU (family U t) N c (n+c) (Y.basicOpen z)).hom ≫ a) h

include H hV hB₁ hB₂ in
theorem recovery (x : group f i U hU t N c n)
    (hx : (OpenRestriction.supportedFunctor U (family U t) c (n+c)).map
      (OpenFixedClass.scalar f i U hU N z) x = x) :
    wideComparison f i U hU t N c n B₁ J₁ r₁ s₁ V T₁ l₁ t₁ x =
      localComparison f i U hU t N z c n B₂ J₂ r₂ s₂ V T₂ l₂ t₂
        (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x) :=
  after_candidate (SupportedCandidate.candidate f i U hU t N z O₁ O₂ H c (n+c))
    (wideComparison f i U hU t N c n B₁ J₁ r₁ s₁ V T₁ l₁ t₁)
    (localComparison f i U hU t N z c n B₂ J₂ r₂ s₂ V T₂ l₂ t₂)
    (candidate_comparison f i U hU t N z O₁ O₂ H c n B₁ J₁ r₁ s₁ B₂ J₂ r₂ s₂
      V hV T₁ l₁ t₁ T₂ l₂ t₂ hB₁ hB₂) x
    (OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N (family U t) c (n+c) x)
    (SupportedCandidate.recovery f i U hU t N z O₁ O₂ H c n x hx)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCover
