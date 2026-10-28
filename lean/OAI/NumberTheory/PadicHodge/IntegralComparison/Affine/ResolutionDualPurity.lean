import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.HomComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomComplexDual
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Transport

/-! # Resolution Dual Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualPurity

noncomputable section

/-! Local duality for the actual internal-Hom complex of a sheaf
resolution, using its affine section resolution and a regular-sequence
presentation of the resolved module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.HomComplex

def algebraicComplexIso :
    (((AffineOpen.HomComplex.algebraicHom U hU N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op) ≅
      (((preadditiveYoneda.obj ((AffineOpen.InternalHom.sections U hU).obj N)).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).obj
          (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K).op) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; rfl)

variable [∀ n, (K.X n).IsQuasicoherent]

def sectionComplexIso :
    (((AffineOpen.HomComplex.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op) ≅
      (((preadditiveYoneda.obj ((AffineOpen.InternalHom.sections U hU).obj N)).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).obj
          (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K).op) := by
  let (n : ℕ) : (K.op.X n).unop.IsQuasicoherent :=
    inferInstanceAs ((K.X n).IsQuasicoherent)
  exact AffineOpen.HomComplex.complexIso U hU N (ComplexShape.down ℕ).symm K.op ≪≫ algebraicComplexIso U hU N K

variable (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ n, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X n))]
  (rs : List Γ(X, U)) (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) rs)
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ IntegralComparison.ProjectiveResolution.DualPurity.quotient Γ(X, U) rs)
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def resolution : ProjectiveResolution (IntegralComparison.ProjectiveResolution.DualPurity.quotient Γ(X, U) rs) :=
  IntegralComparison.ProjectiveResolution.Transport.alongIso
    (AffineOpen.Resolution.ofAugmentation U hU M K ε) eM

def purityIso :
    ((((AffineOpen.HomComplex.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op).homology
      rs.length) ≅
        (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
          (IntegralComparison.ProjectiveResolution.DualPurity.quotient Γ(X, U) rs) :=
  HomologicalComplex.homologyMapIso (sectionComplexIso U hU N K) rs.length ≪≫
    HomComplexDual.Comparison.purityIso Γ(X, U) rs hreg (resolution U hU K M ε rs eM)
      ((AffineOpen.InternalHom.sections U hU).obj N) eN

include ε hreg eM eN in
theorem exactAt (n : ℕ) (hn : n ≠ rs.length) :
    (((AffineOpen.HomComplex.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.homologyMapIso (sectionComplexIso U hU N K) n).isZero_iff.mpr
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (HomComplexDual.Comparison.exactAt Γ(X, U) rs hreg (resolution U hU K M ε rs eM)
      ((AffineOpen.InternalHom.sections U hU).obj N) eN n hn)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualPurity
