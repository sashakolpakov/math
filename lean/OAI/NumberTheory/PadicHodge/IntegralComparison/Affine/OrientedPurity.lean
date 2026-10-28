import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomOrientedPurity

/-! # Oriented Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurity

noncomputable section

/-! Oriented local purity on the actual sections of the cohomology
sheaf of an internal Hom complex. The resolved quotient is fixed before
choosing equations, so the determinant transition compares the same
native cohomology module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (I : Ideal Γ(X, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I))

def resolution : ProjectiveResolution (ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I)) :=
  IntegralComparison.ProjectiveResolution.Transport.alongIso
    (AffineOpen.Resolution.ofAugmentation U hU M K ε) eM

variable [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(X, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def iso :
    (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology c) ≅
        ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I) :=
  LinearResolutionPurity.sectionsHomologyIso U hU N K c ≪≫
    HomologicalComplex.homologyMapIso
      (LinearResolutionPurity.sectionComplexIso U hU N K) c ≪≫
        LinearHomOrientedPurity.iso Γ(X, U) I s hs hreg
          (resolution U hU K M ε I eM) ((AffineOpen.InternalHom.sections U hU).obj N) eN

variable (t : Fin c → Γ(X, U))
  (ht : Koszul.OrientedTopCohomology.ideal Γ(X, U) t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn t))
  (A : Matrix (Fin c) (Fin c) Γ(X, U))
  (hA : ∀ i, s i = ∑ j, A i j * t j)

include hA in
theorem transition : (iso U hU N K M ε I eM s hs hreg eN).hom =
    (iso U hU N K M ε I eM t ht htreg eN).hom ≫
      ModuleCat.ofHom (A.det • (LinearMap.id : (Γ(X, U) ⧸ I) →ₗ[Γ(X, U)] (Γ(X, U) ⧸ I))) := by
  simp only [iso, Iso.trans_hom]
  rw [LinearHomOrientedPurity.transition Γ(X, U) I s hs hreg
    (resolution U hU K M ε I eM) ((AffineOpen.InternalHom.sections U hU).obj N) eN t ht htreg A hA]
  simp only [Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurity
