import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalDualInvariance
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.RefinementMap

/-! # Koszul Resolution Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulResolutionCoordinates

noncomputable section

/-! The native normal-Koszul comparison and the original resolution
comparison have identical cochain maps. Principal restriction also
retains the literal dual resolution maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules)

 theorem dual_map {K L : ChainComplex X.Modules ℕ} (a : K ⟶ L) :
    (((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).map
      ((Affine.LocalDualInvariance.functor N).map a.op)) =
    ((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).map
        ((HomologicalComplex.opFunctor X.Modules (.down ℕ)).map a.op) := rfl

variable [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  (M : X.Modules) [M.IsQuasicoherent]
  (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U)
    (Γ(X, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(X, U) s))

theorem equivalence_hom :
    (Koszul.Comparison.equivalence U hU N e K M ε s hs eM).hom =
      ((Resolution.Comparison.equivalence U hU N e M K ε _ eM
        (KoszulPartial.Resolution.normalResolution Γ(X, U) s hs)).trans
          (HomotopyEquiv.ofIso (KoszulPoint.HomCoordinates.normalIso
            Γ(X, U) (SectionPresheaf.rings U hU) s))).hom := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulResolutionCoordinates
