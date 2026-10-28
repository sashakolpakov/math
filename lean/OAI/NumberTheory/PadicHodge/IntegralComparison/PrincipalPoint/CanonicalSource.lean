import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PulledIntegerRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CanonicalSupportCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions

/-! # Canonical Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.CanonicalSource

noncomputable section

/-! The original point-class comparison agrees with the canonical
source support comparison on its literal pulled projective cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PulledIntegerRefinement

variable {Y X Z T S : Scheme.{0}} [X.IsSeparated] [Z.IsSeparated]
  (f : Y ⟶ X) [IsAffineHom f] (i : X ⟶ Z) [IsClosedImmersion i]
  (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Z.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {c g : ℕ} (s : Fin c → Γ(Z,U)) (t : Fin g → Γ(Z,U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  {κ : Type} [LinearOrder κ] (V : κ → Z.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (N : Y.Modules) [N.IsQuasicoherent]

include f in
private theorem source_separated : Y.IsSeparated := ⟨by
  rw [← terminal.comp_from f]
  infer_instance⟩

local instance pushed_quasicoherent : ((Scheme.Modules.pushforward f).obj N).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f

include hs hst in
private theorem relative_source (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology (PulledIntegerRefinement.ambient f i U hU)
      (PulledIntegerRefinement.complement f i s₀) (PulledIntegerRefinement.common f i s₀ U hU t) (PulledIntegerRefinement.localRight f i s₀ U hU t)
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q) := by
  let := source_separated f
  exact Affine.SingleCechRefinement.relative (PulledIntegerRefinement.ambient f i U hU) (PulledIntegerRefinement.ambient_affine f i U hU)
    (PulledIntegerRefinement.complement f i s₀) (PulledIntegerRefinement.common f i s₀ U hU t) (PulledIntegerRefinement.localRight f i s₀ U hU t)
    (PulledIntegerRefinement.sourceOutside f i s₀ U) (PulledIntegerRefinement.complementary_cover f i s₀ U hU)
    (PulledIntegerRefinement.common_cover f i s₀ U hU s t hs hst)
    (PulledIntegerRefinement.complement_affine f i s₀) (PulledIntegerRefinement.common_affine f i s₀ U hU t) N c q

include hcontains hV haV in
private theorem ordered_source (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap (PulledIntegerRefinement.global f i V)
      (PulledIntegerRefinement.globalCommon f i s₀ U hU V) (PulledIntegerRefinement.globalRight f i s₀ U hU V)
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q) := by
  let := source_separated f
  exact Affine.SingleCechRefinement.ordered (PulledIntegerRefinement.global f i V) (PulledIntegerRefinement.globalCommon f i s₀ U hU V)
    (PulledIntegerRefinement.globalRight f i s₀ U hU V) (PulledIntegerRefinement.global_affine f i V haV)
    (PulledIntegerRefinement.globalCommon_affine f i s₀ U hU V haV) N c
    (PulledIntegerRefinement.global_cover f i V hV) (PulledIntegerRefinement.globalCommon_cover f i s₀ U hU hcontains V hV) q

variable (G : Principal.SectionPresheaf.Index U ⥤ Y.Opens) (P : Y.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU) G
    (Fraction.family U t) (PulledIntegerRefinement.outside f s₀) P)
  [∀ (d : ℕ) (a : Fin (d+1) → ULift (Fin g)),
    PreservesLimit (Discrete.functor (Fraction.family U t ∘ a)) G]

def canonicalComparison :
    (AffinePrincipal.Injective.Comparison.source
      (PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU)
      (Fraction.family U t) N c).homology (g+c) ⟶
    (Affine.OrderedInjective.Comparison.source N c (PulledIntegerRefinement.global f i V)).homology (g+c) := by
  letI := source_separated f
  exact Principal.CanonicalSupportCover.comparison
    (PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU)
    (Fraction.family U t) (PulledIntegerRefinement.outside f s₀)
    H.wide_affine H.wide_punctured H.wide_cover H.wide_global
    N c (PulledIntegerRefinement.global f i V) (PulledIntegerRefinement.global_cover f i V hV) (PulledIntegerRefinement.global_affine f i V haV) (g+c)

omit [∀ (d : ℕ) (a : Fin (d + 1) → ULift.{0, 0} (Fin g)), PreservesLimit (Discrete.functor (Fraction.family U t ∘ a)) G] in
theorem sourceComparison_eq :
    Source.Comparison.sourceComparison f i s₀ U hU hcontains s t hs hst V hV haV N =
      canonicalComparison (c := c) f i s₀ U hU t V hV haV N G P H := by
  let := source_separated f
  let : IsIso (RelativeCech.Refinement.homology
      ((PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU).obj (⊤_ _))
      (PulledIntegerRefinement.complement f i s₀) (PulledIntegerRefinement.common f i s₀ U hU t) (PulledIntegerRefinement.localRight f i s₀ U hU t)
      (Affine.OrderedInjective.Comparison.sourcePresheaf N c) (g+c)) :=
    relative_source f i s₀ U hU s t hs hst N (g+c)
  let := ordered_source (c := c) f i s₀ U hU hcontains V hV haV N (g+c)
  let : IsIso (RelativeCech.Refinement.homology
      ((PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU).obj (⊤_ _))
      (PulledIntegerRefinement.complement f i s₀) (PulledIntegerRefinement.common f i s₀ U hU t) (PulledIntegerRefinement.localRight f i s₀ U hU t)
      (Affine.OrderedInjective.Comparison.integerPresheaf N c) (g+c)) :=
    PulledIntegerRefinement.relative_integer
      f i s₀ U hU s t hs hst N c (g+c)
  let := PulledIntegerRefinement.ordered_integer
    f i s₀ U hU hcontains V hV haV N c (g+c)
  have h := Principal.CanonicalSupportCover.SingleIndependence.comparison
    (PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU) G
    (Fraction.family U t) (PulledIntegerRefinement.outside f s₀) P H N c
    (PulledIntegerRefinement.global f i V) (PulledIntegerRefinement.global_cover f i V hV) (PulledIntegerRefinement.global_affine f i V haV) (g+c)
    (PulledIntegerRefinement.complement f i s₀) (PulledIntegerRefinement.common f i s₀ U hU t)
    (RelativeCech.Reindex.mapped (f ≫ i).base
      ((Principal.AdditiveSections.opens U hU).obj ∘ Fraction.family U t)
      (RelativeGeometry.common i s₀ U hU t)
      (RelativeGeometry.left i s₀ U hU t))
    (PulledIntegerRefinement.localRight f i s₀ U hU t) (PulledIntegerRefinement.globalCommon f i s₀ U hU V)
    (RelativeCech.ReindexGlobal.leftRefinement (f ≫ i).base (Principal.RelativeConcentration.ambient U hU)
      (RelativeGeometry.complementary i s₀)
      (PointComplementGlobalCover.common (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU) V)
      (PointComplementGlobalCover.left (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU) V))
    (PulledIntegerRefinement.globalRight f i s₀ U hU V) (PulledIntegerRefinement.complement_below f i s₀)
  exact h

variable (π : Z ⟶ S)

omit [∀ (d : ℕ) (a : Fin (d + 1) → ULift.{0, 0} (Fin g)), PreservesLimit (Discrete.functor (Fraction.family U t ∘ a)) G] in
theorem comparison_apply
    (x : (Source.Comparison.localTotal (c := c) f i U hU t N).homology (c+g)) :
    Source.Comparison.sourceOutput (c := c) (g := g) f i π V N
      (Source.Comparison.ordinaryMap f i π s₀ U hU hcontains s t hs hst
        V hV haV N (c+g) (Nat.add_comm c g) x) =
    canonicalComparison (c := c) f i s₀ U hU t V hV haV N G P H
      (PrincipalSource.ClassCoordinates.wideClass f i U hU N t c x) := by
  have h := Source.Comparison.comparison_apply f i π s₀ U hU hcontains
    s t hs hst V hV haV N x
  rw [sourceComparison_eq f i s₀ U hU hcontains s t hs hst V hV haV N G P H] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.CanonicalSource
