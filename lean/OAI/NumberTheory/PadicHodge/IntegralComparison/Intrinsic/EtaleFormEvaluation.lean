import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormDualEvaluation

/-! # Etale Form Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormEvaluation

noncomputable section

/-! Actual source module-form sections are the coefficient dual of
actual target module-form sections. Evaluation at one agrees with the
original global finite étale de Rham trace through its native comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormDuality

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] (U : Y.left.Opens) [Fact (IsAffineOpen U)]

local instance : Algebra (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R X Y f U
local instance : IsScalarTower R (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionTower R X Y f U
local instance : Algebra.Etale (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sectionEtale R X Y f U Fact.out

variable (σ : Type u) [Fintype σ] [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
  [IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]
  [Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)]

local instance : Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.polynomialSource R X Y f U σ
local instance : IsScalarTower (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.polynomialTower R X Y f U σ
local instance : IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.polynomialBaseTower R X Y f U σ
local instance : Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.sourceRing R X Y f U) :=
  AffineOpen.DeRhamTrace.sourceEtale R X Y f U σ

local instance sourceScalar (n : ℕ) : Module (AffineOpen.DeRhamTrace.sourceRing R X Y f U) (EtaleFormDuality.sourceSections R X Y f U n) :=
  inferInstanceAs (Module Γ(X.left, f.left ⁻¹ᵁ U) (EtaleFormDuality.sourceSections R X Y f U n))
local instance targetScalar (n : ℕ) : Module (AffineOpen.DeRhamTrace.targetRing R Y U) (EtaleFormDuality.targetSections R Y U n) :=
  inferInstanceAs (Module Γ(Y.left, U) (EtaleFormDuality.targetSections R Y U n))
local instance restrictedScalar (n : ℕ) : Module (AffineOpen.DeRhamTrace.targetRing R Y U) (EtaleFormDuality.sourceSections R X Y f U n) :=
  Module.compHom (EtaleFormDuality.sourceSections R X Y f U n) (algebraMap (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U))
local instance (n : ℕ) : IsScalarTower (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)
    (EtaleFormDuality.sourceSections R X Y f U n) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

variable [Module.Free (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)]
  [Module.Finite (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)]

omit [Fintype σ] in
theorem smul (n : ℕ) (b x : AffineOpen.DeRhamTrace.sourceRing R X Y f U) (z : EtaleFormDuality.sourceSections R X Y f U n) :
    EtaleFormDuality.equiv R X Y f U σ n (b • z) x = EtaleFormDuality.equiv R X Y f U σ n z (b * x) := by
  obtain ⟨ω, rfl⟩ := IntegralComparison.Etale.FormSections.Integral.unit_bijective R X (f.left ⁻¹ᵁ U)
    ((Fact.out : IsAffineOpen U).preimage f.left) σ n |>.surjective z
  rw [← (Integral.FormSectionUnit.unit R X n (f.left ⁻¹ᵁ U)).map_smul,
    EtaleFormDuality.equiv_unit, EtaleFormDuality.equiv_unit, IntegralComparison.Etale.FormDualEvaluation.smul]

variable [IsProper Y.hom] [Smooth Y.hom]

theorem evaluation (n : ℕ) (b : AffineOpen.DeRhamTrace.sourceRing R X Y f U) (z : EtaleFormDuality.sourceSections R X Y f U n) :
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y U n).hom (EtaleFormDuality.equiv R X Y f U σ n z b) =
      ((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f n).hom.app (op U)
        ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ U) n).hom (b • z)) := by
  calc
    _ = (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y U n).hom
        (EtaleFormDuality.equiv R X Y f U σ n (b • z) 1) := by rw [smul, mul_one]
    _ = _ := EtaleFormDuality.global_trace R X Y f U σ
      (Module.Free.chooseBasis (AffineOpen.DeRhamTrace.targetRing R Y U) (AffineOpen.DeRhamTrace.sourceRing R X Y f U)) n (b • z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormEvaluation
