import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormRestriction

/-! # Etale Form Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormRestriction

noncomputable section

/-! The native finite étale form duality preserves actual restriction,
including a change of the polynomial coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis
open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormDuality

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]

local instance (U : Y.left.Opens) (n : ℕ) : Module (AffineOpen.DeRhamTrace.sourceRing R X Y f U)
    (EtaleFormDuality.sourceSections R X Y f U n) :=
  inferInstanceAs (Module Γ(X.left, f.left ⁻¹ᵁ U) (EtaleFormDuality.sourceSections R X Y f U n))

local instance (a : FiniteEtale.TraceBasis.Index R X Y f) : LinearOrder (FiniteEtale.TraceBasis.coordinateIndex R X Y f a) :=
  FiniteEtale.TraceBasis.coordinateOrder R X Y f a

def localEquiv (a : FiniteEtale.TraceBasis.Index R X Y f) (n : ℕ) :=
  EtaleFormDuality.equiv R X Y f (FiniteEtale.TraceBasis.opens R X Y f a) (FiniteEtale.TraceBasis.coordinateIndex R X Y f a) n

variable [IsProper Y.hom] [Smooth Y.hom]

theorem evaluation (a : FiniteEtale.TraceBasis.Index R X Y f) (n : ℕ)
    (b : AffineOpen.DeRhamTrace.sourceRing R X Y f a.val) (z : EtaleFormDuality.sourceSections R X Y f a.val n) :
    (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y a.val n).hom (localEquiv R X Y f a n z b) =
      ((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f n).hom.app (op a.val)
        ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ a.val) n).hom (b • z)) :=
  EtaleFormEvaluation.evaluation R X Y f a.val (FiniteEtale.TraceBasis.coordinateIndex R X Y f a) n b z

theorem restriction (a b : FiniteEtale.TraceBasis.Index R X Y f) (h : b.val ≤ a.val) (n : ℕ)
    (z : EtaleFormDuality.sourceSections R X Y f a.val n) (m : AffineOpen.DeRhamTrace.sourceRing R X Y f a.val) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y n).presheaf.map (homOfLE h).op
      (localEquiv R X Y f a n z m) =
    localEquiv R X Y f b n
      ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map
        ((TopologicalSpace.Opens.map f.left.base).map (homOfLE h)).op z)
      (X.left.presheaf.map ((TopologicalSpace.Opens.map f.left.base).map (homOfLE h)).op m) := by
  apply (ConcreteCategory.bijective_of_isIso (Integral.IntrinsicFormNormalization.Intrinsic.iso R Y b.val n).hom).injective
  rw [Integral.IntrinsicFormRestriction.Intrinsic.restriction, evaluation, evaluation,
    ← Integral.IntrinsicFormRestriction.Intrinsic.restriction_smul,
    Integral.IntrinsicFormRestriction.Intrinsic.restriction]
  exact (ConcreteCategory.congr_hom
    (((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f n).hom.naturality (homOfLE h).op)
      ((Integral.IntrinsicFormNormalization.Intrinsic.iso R X (f.left ⁻¹ᵁ a.val) n).hom (m • z))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleFormRestriction
