import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleBaseCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleModuleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry

/-! # Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SingleCoordinates

noncomputable section

/-! The genuine point-complement geometry identifies the original
single-sheaf transfer with the ordinary principal coefficient map.
Every refinement inverse is supplied by the original closed point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
variable {X Y T S : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
  (π : Y ⟶ S) (i : X ⟶ Y) [IsClosedImmersion i] (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Y.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {a g : ℕ} (s : Fin a → Γ(Y,U)) (t : Fin g → Γ(Y,U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  {κ : Type u} [LinearOrder κ] (V : κ → Y.Opens) (hV : iSup V = ⊤)
  (haV : ∀ j, IsAffineOpen (V j)) (N : X.Modules) [N.IsQuasicoherent]
  (c q : ℕ) (hq : q=g+c)

abbrev coefficient := (Scheme.Modules.pushforward i).obj N
abbrev family := Fraction.family U t

local instance coefficient_qc : (coefficient i N).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
local instance single_qc (k : ℕ) :
    (((single Y.Modules (.up ℕ) c).obj (coefficient i N)).X k).IsQuasicoherent :=
  QuasicoherentTruncation.single (coefficient i N) c k

include hs hst in
private theorem refinement_isIso :
    IsIso (RelativeCech.Refinement.homology
      (Principal.RelativeConcentration.ambient U hU) (RelativeGeometry.complementary i s₀)
      (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t)
      (Relative.AdditiveCechConcentration.coefficients
        ((single Y.Modules (.up ℕ) c).obj (coefficient i N))) q) :=
  RelativeGeometry.right_isIso i s₀ U hU s t hs hst
    ((single Y.Modules (.up ℕ) c).obj (coefficient i N)) c
    (fun k hk => exactAt_single_obj (.up ℕ) c (coefficient i N) k hk) N
    (singleObjHomologySelfIso (.up ℕ) c (coefficient i N)) q

def originalMap := by
  letI := refinement_isIso i s₀ U hU s t hs hst N c q
  exact PrincipalReference.CoverTransfer.Reference.comparison U hU (family U t) (s₀ ≫ i) hcontains
      (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.left i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t) V hV haV
      (K := (single Y.Modules (.up ℕ) c).obj (coefficient i N)) q ≫
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
      ((single Y.Modules (.up ℕ) c).obj (coefficient i N)) q).inv ≫
    (Global.PureIndexedCoordinates.singleIso π V (coefficient i N) c g q hq).hom

def coefficientComparison := by
  letI := refinement_isIso i s₀ U hU s t hs hst N c q
  exact (Principal.SingleModuleCoordinates.coefficientIso U hU (coefficient i N) (family U t) g).hom ≫
    PrincipalReference.SingleBaseCoordinates.Reference.coefficientComparison π U hU (family U t)
      (s₀ ≫ i) hcontains (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.left i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t)
      V hV haV (coefficient i N) c g q hq

theorem comparison :
    originalMap π i s₀ U hU hcontains s t hs hst V hV haV N c q hq =
      (Principal.AdditiveSections.forgetScalars U).map
        (homologyMap (Principal.SingleModuleCoordinates.singleMap U hU
          (coefficient i N) c (family U t)) q) ≫
      (Principal.AdditiveSections.forgetScalars U).map
        (Principal.SingleModuleCoordinates.moduleCoordinates U hU (coefficient i N) c
          (family U t) g q hq).hom ≫
      coefficientComparison π i s₀ U hU hcontains s t hs hst V hV haV N c q hq := by
  let := refinement_isIso i s₀ U hU s t hs hst N c q
  have h := PrincipalReference.SingleBaseCoordinates.Reference.comparison π U hU (family U t)
    (s₀ ≫ i) hcontains (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.left i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t)
    V hV haV (coefficient i N) c g q hq
  rw [Principal.SingleModuleCoordinates.factor] at h
  simpa only [originalMap, coefficientComparison, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SingleCoordinates
