import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHomComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.LineFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientNaturality

/-! # Framed Hom Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomComplex

noncomputable section

/-! The original internal-Hom section complex, trivialized by one
ambient target frame, on every principal subopen at once. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex X.Modules c)
  [∀ n, (K.X n).IsQuasicoherent]

local instance sections_additive : (AffineOpen.InternalHom.sections U hU).Additive where
  map_add {_M _N} _f _g := rfl

local instance op_qc (n : ι) : (K.op.X n).unop.IsQuasicoherent :=
  show (K.X n).IsQuasicoherent from inferInstance

abbrev sections := ((Affine.ModuleExactSections.sections U).mapHomologicalComplex c).obj K

def literalIso :
    (((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex c.symm).obj K.op) ≅
      HomCoefficientFunctor.complex Γ(X, U) (SectionPresheaf.modules U hU N) (sections U c K) :=
  InternalHomComplex.iso U hU N c.symm K.op

def iso :
    (((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex c.symm).obj K.op) ≅
      HomCoefficientFunctor.complex Γ(X, U) (LineFrame.scalars U hU)
        (sections U c K) :=
  literalIso U hU N c K ≪≫
    HomCoefficientNaturality.complexIso Γ(X, U) (LineFrame.iso U hU N e)
      (sections U c K)

def chartIso : sections U c K ≅
    ((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex c).obj K :=
  (NatIso.mapHomologicalComplex (AffineOpen.LinearHom.sectionsIso U hU) c).app K

def chartHomIso :
    HomCoefficientFunctor.complex Γ(X, U) (LineFrame.scalars U hU)
      (sections U c K) ≅
    HomCoefficientFunctor.complex Γ(X, U) (LineFrame.scalars U hU)
      (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex c).obj K) :=
  ((HomCoefficientFunctor.functor Γ(X, U) (LineFrame.scalars U hU)).mapHomologicalComplex
    c.symm).mapIso (HomologicalComplex.opFunctor _ c |>.mapIso (chartIso U hU c K).symm.op)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomComplex
