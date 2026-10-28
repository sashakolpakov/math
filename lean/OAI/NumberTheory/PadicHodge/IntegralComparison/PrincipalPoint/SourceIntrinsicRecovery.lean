import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.CanonicalSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicRecovery
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassFixed

/-! # Source Intrinsic Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SourceIntrinsicRecovery.Intrinsic

noncomputable section

/-! The original point-class comparison has its exact native local
image on the selected source neighborhood, with the original degree
transport and coefficient fixedness retained. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PulledIntegerRefinement

private theorem paste {A : Type*} {x y y' z z' : A}
    (h : x = y) (h' : y' = z') (hy : y = y') (hz : z' = z) : x = z :=
  h.trans (hy.trans (h'.trans hz))

variable {Y X Z T S : Scheme.{0}} [Y.IsSeparated] [X.IsSeparated] [Z.IsSeparated]
  (f : Y ⟶ X) [IsAffineHom f] (i : X ⟶ Z) [IsClosedImmersion i]
  (π : Z ⟶ S) (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Z.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {c g : ℕ} (s : Fin c → Γ(Z,U)) (t : Fin g → Γ(Z,U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  {κ : Type} [LinearOrder κ] (V : κ → Z.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (N : Y.Modules) [N.IsQuasicoherent]
  (z : Γ(Y,(f ≫ i) ⁻¹ᵁ U)) (O : Y.Opens)
  (H : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (PrincipalSource.OpenReindex.wideOpens (f ≫ i) U hU)
    (PrincipalSource.OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z))
    (Fraction.family U t) (PulledIntegerRefinement.outside f s₀) O)
  (hza : IsAffineOpen (Y.basicOpen z)) (hZU : Y.basicOpen z ≤ (f ≫ i) ⁻¹ᵁ U)

local instance pushed_quasicoherent : ((Scheme.Modules.pushforward f).obj N).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f

variable (x : (PrincipalSource.ClassCoordinates.total f i U hU N t c).homology (c+g))
  (hx : (PrincipalSource.OpenRestriction.supportedFunctor U
      (Fraction.family U t) c (c+g)).map
        (PrincipalSource.OpenFixedClass.scalar f i U hU N z) x = x)

include hx in
theorem recovery :
    Source.Comparison.sourceOutput (c := c) (g := g) f i π V N
      (Source.Comparison.ordinaryMap f i π s₀ U hU hcontains s t hs hst
        V hV haV N (c+g) (Nat.add_comm c g) x) =
    PrincipalSource.IntrinsicRecovery.Intrinsic.nativeComparison f i U hU t N z (PulledIntegerRefinement.outside f s₀) O H hza hZU
      c g (PulledIntegerRefinement.global f i V) (PulledIntegerRefinement.global_cover f i V hV) (PulledIntegerRefinement.global_affine f i V haV)
      (PrincipalSource.ClassCoordinates.nativeClass f i U hU N t c
        (Y.basicOpen z) hza hZU x) := by
  have ho := CanonicalSource.comparison_apply f i s₀ U hU hcontains s t hs hst
    V hV haV N (PrincipalSource.OpenReindex.geometricOpens (f ≫ i) U hU (Y.basicOpen z)) O H π x
  have hfixed := PrincipalSource.ClassFixed.Coordinates.cast_fixed f i U hU N t c
    (PrincipalSource.OpenFixedClass.scalar f i U hU N z) x hx
  have hn := PrincipalSource.IntrinsicRecovery.Intrinsic.recovery f i U hU t N z (PulledIntegerRefinement.outside f s₀) O H hza hZU
    c g (PulledIntegerRefinement.global f i V) (PulledIntegerRefinement.global_cover f i V hV) (PulledIntegerRefinement.global_affine f i V haV)
    (PrincipalSource.ClassCoordinates.cast f i U hU N t c x) hfixed
  refine paste ho hn ?_ ?_
  · as_aux_lemma => rfl
  · as_aux_lemma => rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SourceIntrinsicRecovery.Intrinsic
