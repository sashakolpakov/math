import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Transport
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomotopyNaturality

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution.Comparison

noncomputable section

/-! Actual augmentation-preserving sheaf resolution maps compare
canonically to any local projective resolutions on the entire principal
diagram, by a genuine cochain homotopy. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def resolution (M : X.Modules) [M.IsQuasicoherent]
    (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
    (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
    [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
    (T : ModuleCat.{u} Γ(X, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T) : ProjectiveResolution T :=
  IntegralComparison.ProjectiveResolution.Transport.alongIso
    (AffineOpen.Resolution.ofAugmentation U hU M K ε) eM

variable (N : X.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  (M : X.Modules) [M.IsQuasicoherent]
  (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (T : ModuleCat.{u} Γ(X, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T)
  (P : ProjectiveResolution T)

def equivalence : HomotopyEquiv
    (((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj K.op)
    (HomCoefficientFunctor.complex Γ(X, U) (LineFrame.scalars U hU) P.complex) :=
  (HomotopyEquiv.ofIso (FramedHomNaturality.iso U hU N e (.down ℕ) K)).trans
    (IntegralComparison.ProjectiveResolution.Hom.Comparison.homotopyEquiv
      (HomCoefficientFunctor.functor Γ(X, U) (LineFrame.scalars U hU))
      (resolution U hU M K ε T eM) P)

variable (M' : X.Modules) [M'.IsQuasicoherent]
  (L : ChainComplex X.Modules ℕ) [∀ q, (L.X q).IsQuasicoherent]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (T' : ModuleCat.{u} Γ(X, U)) (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ T')
  (Q : ProjectiveResolution T') (f : K ⟶ L) (b : T ⟶ T')
  (a : P.complex ⟶ Q.complex)
  (hf : (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map f) ≫
      (resolution U hU M' L ε' T' eM').π =
    (resolution U hU M K ε T eM).π ≫ (ChainComplex.single₀ _).map b)
  (ha : a ≫ Q.π = P.π ≫ (ChainComplex.single₀ _).map b)

def naturality : Homotopy
    (((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).map
          ((HomologicalComplex.opFunctor X.Modules (.down ℕ)).map f.op) ≫
        (equivalence U hU N e M K ε T eM P).hom)
    ((equivalence U hU N e M' L ε' T' eM' Q).hom ≫
      HomCoefficientFunctor.map Γ(X, U) (LineFrame.scalars U hU) a) := by
  let F := HomCoefficientFunctor.functor Γ(X, U) (LineFrame.scalars U hU)
  let h := IntegralComparison.ProjectiveResolution.HomotopyNaturality.naturality F b
    (resolution U hU M K ε T eM) P (resolution U hU M' L ε' T' eM') Q
    (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map f) a hf ha
  let iK := FramedHomNaturality.iso U hU N e (.down ℕ) K
  let iL := FramedHomNaturality.iso U hU N e (.down ℕ) L
  change Homotopy (_ ≫ (iK.hom ≫ _)) ((iL.hom ≫ _) ≫ _)
  exact (Homotopy.ofEq (by
    rw [← Category.assoc, FramedHomNaturality.naturality,
      Category.assoc]
    rfl)).trans
    ((h.compLeft iL.hom).trans (Homotopy.ofEq (Category.assoc _ _ _).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution.Comparison
