import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFractionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafIso

/-! # Fraction Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FractionClass.Integral

noncomputable section

/-! The actual integral sheaf-form fraction represents the weighted
original supported crystalline residue under the canonical comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.coefficients p k

def target : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) L).mapHomologicalComplex (.up ℕ)).obj
    (PrincipalSheafIso.target p k n X U)

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

def iso : Principal.Comparison.source p k n X Y f hp U ≅ target p k n X U :=
  PrincipalFractionClass.iso p k n X Y f hp U ≪≫
    ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) L).mapHomologicalComplex (.up ℕ)).mapIso
      (PrincipalSheafIso.iso p k n X U σ)

variable (g : ℕ) (a : Fin g → Γ(X.left, U.val))

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.family p k Y Q g a
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDComplex.topCoefficient p k Y Q g a
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFraction.topOpen p k n X Y f hp U g a

def fraction (r : WittVector p k) : ((target p k n X U).X g).obj (op t) :=
  ⟨⟨(Integral.IntrinsicFormNormalization.Intrinsic.iso S X (O).val g).hom
    (Integral.FormSectionUnit.unit S X g (O).val
      (PrincipalFraction.fraction p k n X Y f hp U g a r))⟩⟩

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem map_weightedForm (r : WittVector p k) :
    (((iso p k n X Y f hp U σ).hom.f g).app (op t))
        ((⟨r⟩ : R) • ResidueClass.form p k n X Y f hp U g a) =
      fraction p k n X Y f hp U g a r := by
  change (((((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) L).mapHomologicalComplex (.up ℕ)).map
      (PrincipalSheafIso.iso p k n X U σ).hom).f g).app (op t))
    ((((PrincipalFractionClass.iso p k n X Y f hp U).hom.f g).app (op t))
      ((⟨r⟩ : R) • ResidueClass.form p k n X Y f hp U g a)) = _
  erw [PrincipalFractionClass.map_weightedForm p k n X Y f hp U g a r]
  exact congrArg (fun z => ULift.up.{2,1} (ULift.up.{1,0} z))
    (PrincipalSheafIso.integral_unit p k n X U σ g t
      (PrincipalFraction.fraction p k n X Y f hp U g a r))

include σ in
omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem fraction_closed (r : WittVector p k) :
    ((target p k n X U).d g (g + 1)).app (op t)
      (fraction p k n X Y f hp U g a r) = 0 := by
  rw [← map_weightedForm p k n X Y f hp U σ g a r]
  apply AugmentedOrdered.CechCoefficientTop.mapped_coefficient_closed V
    (iso p k n X Y f hp U σ).hom g (by simp) g
  erw [map_smul, ResidueClass.form_closed p k n X Y f hp U g a, smul_zero]

def fractionClass (r : WittVector p k) :=
  AugmentedOrdered.CechLargeTop.topTotalClass V (target p k n X U) g (by simp) g
    (fraction p k n X Y f hp U g a r) (fraction_closed p k n X Y f hp U σ g a r)

abbrev inverse_class (r : WittVector p k) :=
  AugmentedCech.WeightedIso.inverse_class V (iso p k n X Y f hp U σ) g (by simp) g
    (ResidueClass.form p k n X Y f hp U g a)
    (ResidueClass.form_closed p k n X Y f hp U g a) (⟨r⟩ : R)
    (fraction p k n X Y f hp U g a r) (fraction_closed p k n X Y f hp U σ g a r)
    (map_weightedForm p k n X Y f hp U σ g a r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FractionClass.Integral
