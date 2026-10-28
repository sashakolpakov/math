import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomCoefficientComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution

/-! # Koszul -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Koszul.Comparison

noncomputable section

/-! The original augmented affine sheaf resolution and the normal
Koszul resolution have homotopy equivalent Hom complexes on the whole
native principal-open diagram. No choice of separate comparisons on
individual intersections is made. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U)
    (Γ(X, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(X, U) s))

abbrev nativeComplex :=
  (((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex
    (ComplexShape.down ℕ).symm).obj K.op)

def equivalence : HomotopyEquiv (nativeComplex U hU N K)
    (Koszul.HomPresheaf.complex Γ(X, U) (Fin c → Γ(X, U))
      (LineFrame.scalars U hU) (Koszul.GeneratorMatrix.equation Γ(X, U) s)) := by
  let P := Affine.OrientedPurity.resolution U hU K M ε
    (KoszulPartial.Resolution.normalIdeal Γ(X, U) s) eM
  let Q := KoszulPartial.Resolution.normalResolution Γ(X, U) s hs
  let F := HomCoefficientFunctor.functor Γ(X, U) (LineFrame.scalars U hU)
  let e₁ := (FramedHomComplex.iso U hU N e (.down ℕ) K) ≪≫
    FramedHomComplex.chartHomIso U hU (.down ℕ) K
  let e₂ := ProjectiveResolution.Hom.Comparison.homotopyEquiv F P Q
  let e₃ := Koszul.HomCoefficientComplex.iso Γ(X, U) (Fin c → Γ(X, U))
    (LineFrame.scalars U hU) (Koszul.GeneratorMatrix.equation Γ(X, U) s)
  exact ((HomotopyEquiv.ofIso e₁).trans e₂).trans (HomotopyEquiv.ofIso e₃)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Koszul.Comparison
