import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ResolutionHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarAmbient

/-! # Koszul -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul.Comparison

noncomputable section

/-! The actual product point comparison and the concatenated-equation
comparison give the same scalar coordinate of the original resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c m : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin m → Γ(Y, U))
  (hst : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn (Fin.append s t)))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t))

abbrev productCoordinates :=
  (Principal.Resolution.Comparison.equivalence U hU N e M K ε _ eM
    (KoszulPartial.Resolution.pointResolution Γ(Y, U) s t hst)).trans
      (HomotopyEquiv.ofIso (KoszulPoint.HomCoordinates.pointIso Γ(Y, U) (Principal.SectionPresheaf.rings U hU) s t))

abbrev fullCoordinates :=
  (Principal.Resolution.Comparison.equivalence U hU N e M K ε _ eM
    (KoszulPoint.Resolution.Comparison.fullResolution Γ(Y, U) s t hst)).trans
      (HomotopyEquiv.ofIso (Koszul.HomCoefficientComplex.iso Γ(Y, U)
        (Fin (c+m) → Γ(Y, U)) (Principal.LineFrame.scalars U hU)
        (Koszul.GeneratorMatrix.equation Γ(Y, U) (Fin.append s t))))

def homotopy : Homotopy (productCoordinates U hU N e M K ε s t hst eM).hom
    (fullCoordinates U hU N e M K ε s t hst eM).hom := by
  let F := HomCoefficientFunctor.functor Γ(Y, U) (Principal.LineFrame.scalars U hU)
  let P := Principal.Resolution.Comparison.resolution U hU M K ε _ eM
  let a := (Principal.FramedHomNaturality.iso U hU N e (.down ℕ) K).hom
  let b := (Koszul.HomCoefficientComplex.iso Γ(Y, U) (Fin (c+m) → Γ(Y, U))
    (Principal.LineFrame.scalars U hU)
    (Koszul.GeneratorMatrix.equation Γ(Y, U) (Fin.append s t))).hom
  let h := KoszulPoint.ResolutionHomotopy.homotopy Γ(Y, U) s t hst F P
  exact ((h.compLeft a).compRight b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul.Comparison
