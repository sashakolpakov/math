import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionDualPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomDualPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology

/-! # Linear Resolution Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity

noncomputable section

/-! Local purity for the actual cohomology sheaf, with its full action
by the ring of functions on the affine open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom

def algebraicComplexIso :
    (((AffineOpen.LinearHom.algebraicHom U hU N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op) ≅
      ((((linearYoneda Γ(X, U) (ModuleCat Γ(X, U))).obj ((AffineOpen.InternalHom.sections U hU).obj N)).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).obj
          (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K).op) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intros; rfl)

variable [∀ n, (K.X n).IsQuasicoherent]

def sectionComplexIso :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op) ≅
      ((((linearYoneda Γ(X, U) (ModuleCat Γ(X, U))).obj ((AffineOpen.InternalHom.sections U hU).obj N)).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).obj
          (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K).op) := by
  let (n : ℕ) : (K.op.X n).unop.IsQuasicoherent :=
    inferInstanceAs ((K.X n).IsQuasicoherent)
  exact AffineOpen.LinearHom.complexIso U hU N (ComplexShape.down ℕ).symm K.op ≪≫ algebraicComplexIso U hU N K

variable (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ n, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X n))]
  (rs : List Γ(X, U)) (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) rs)
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ProjectiveResolution.DualPurity.quotient Γ(X, U) rs)
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def purityIso :
    ((((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op).homology
      rs.length) ≅ ProjectiveResolution.DualPurity.quotient Γ(X, U) rs :=
  HomologicalComplex.homologyMapIso (sectionComplexIso U hU N K) rs.length ≪≫
    LinearHomDualPurity.purityIso Γ(X, U) rs hreg
      (ResolutionDualPurity.resolution U hU K M ε rs eM)
      ((AffineOpen.InternalHom.sections U hU).obj N) eN

abbrev internalComplex := SchemeInternalHom.complex (ComplexShape.down ℕ).symm N K.op

variable [∀ n, ((internalComplex N K).X n).IsQuasicoherent]

def sectionsHomologyIso (n : ℕ) :
    (ModuleExactSections.sections U).obj ((internalComplex N K).homology n) ≅
      ((((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op).homology n) := by
  let T := (internalComplex N K).sc n
  letI : T.X₁.IsQuasicoherent := inferInstanceAs
    (((internalComplex N K).X ((ComplexShape.down ℕ).symm.prev n)).IsQuasicoherent)
  letI : T.X₂.IsQuasicoherent := inferInstanceAs (((internalComplex N K).X n).IsQuasicoherent)
  letI : T.X₃.IsQuasicoherent := inferInstanceAs
    (((internalComplex N K).X ((ComplexShape.down ℕ).symm.next n)).IsQuasicoherent)
  exact (ModuleHomology.iso U hU T).symm

def cohomologySheafIso :
    (ModuleExactSections.sections U).obj ((internalComplex N K).homology rs.length) ≅
      ProjectiveResolution.DualPurity.quotient Γ(X, U) rs :=
  sectionsHomologyIso U hU N K rs.length ≪≫ purityIso U hU N K M ε rs hreg eM eN

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity
