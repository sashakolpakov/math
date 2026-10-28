import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOrdinaryMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DeRhamSectionUnit

/-! # Principal Sheaf Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafIso

noncomputable section

/-! The actual principal ordinary complex over the truncated base maps
to the original sheaf de Rham sections with their Witt scalar action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  (U : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => ModuleCat.restrictScalars (algebraMap W S)
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) F

def target : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  ((H).mapHomologicalComplex (.up ℕ)).obj (Principal.DeRhamSectionUnit.target S X U)

def ordinaryIso : PrincipalOrdinaryMap.Ordinary.target p k n X U ≅
    ((H).mapHomologicalComplex (.up ℕ)).obj (Principal.DeRhamSectionUnit.source S X U) :=
  GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F
    (IndexedOrdinaryCech.Ordinary.diagram S X (Principal.DeRhamSectionUnit.opens S X U))

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

def iso : PrincipalOrdinaryMap.Ordinary.target p k n X U ≅ target p k n X U :=
  ordinaryIso p k n X U ≪≫ ((H).mapHomologicalComplex (.up ℕ)).mapIso
    (Principal.DeRhamSectionUnit.iso S X U σ)

omit [Fintype k] [CharP k p] in
theorem component (q : ℕ) (r : PrincipalFrame.Index X.left U)
    (x : ((PrincipalOrdinaryMap.Ordinary.target p k n X U).X q).obj (op r)) :
    (((iso p k n X U σ).hom.f q).app (op r)) x =
      ((Principal.DeRhamSectionUnit.map S X U).f q).app (op r) x := rfl

omit [Fintype k] [CharP k p] in
theorem integral_unit (q : ℕ) (r : PrincipalFrame.Index X.left U)
    (x : ((PrincipalOrdinaryMap.Ordinary.target p k n X U).X q).obj (op r)) :
    (((iso p k n X U σ).hom.f q).app (op r)) x =
      (Integral.IntrinsicFormNormalization.Intrinsic.iso S X ((Principal.DeRhamSectionUnit.opens S X U).obj r) q).hom
        (Integral.FormSectionUnit.unit S X q ((Principal.DeRhamSectionUnit.opens S X U).obj r) x) :=
  (component p k n X U σ q r x).trans (Principal.DeRhamSectionUnit.integral_unit S X U q r x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafIso
