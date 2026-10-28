import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassZeroCriterion
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassMonoid

/-! # Class Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel

noncomputable section

section

/-! The actual infinitesimal kernel of algebraic line-bundle
isomorphism classes has representatives with constructed reduced frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

def dualLineClassKernel (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Subgroup (HilbertConstruction.Line.Bundles.LineBundle.IsoClass (LieRanks.dualNumberTest ℂ ⊗ X).left) :=
  (HilbertConstruction.Line.Bundles.LineBundle.pullbackClassMonoidHom (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).ker

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def dualLineClassKernelOfLine (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) :
    dualLineClassKernel X := ⟨HilbertConstruction.Line.Bundles.LineBundle.classOf L, Quotient.sound ⟨e⟩⟩

def dualLineKernelRepresentative (q : dualLineClassKernel X) : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left :=
  Quotient.out q.val

theorem dualLineKernelRepresentative_class (q : dualLineClassKernel X) :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (dualLineKernelRepresentative X q) = q.val := Quotient.out_eq q.val

theorem dualLineKernelRepresentative_frame (q : dualLineClassKernel X) :
    Nonempty ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj
      (dualLineKernelRepresentative X q).sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) := by
  have h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (dualLineKernelRepresentative X q)) = HilbertConstruction.Line.Bundles.LineBundle.trivialClass X.left :=
    (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left)
      (dualLineKernelRepresentative_class X q)).trans q.property
  exact Quotient.exact h

def dualLineKernelFrame (q : dualLineClassKernel X) :
    (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj
      (dualLineKernelRepresentative X q).sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left :=
  (dualLineKernelRepresentative_frame X q).some

theorem dualLineKernelRepresentative_recovers (q : dualLineClassKernel X) :
    dualLineClassKernelOfLine X (dualLineKernelRepresentative X q) (dualLineKernelFrame X q) = q :=
  Subtype.ext (dualLineKernelRepresentative_class X q)

end

/-! The constructed algebraic deformation class descends to the
actual kernel of reduction on line-bundle isomorphism classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

def dualLineKernelCohomology (q : dualLineClassKernel X) : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 :=
  DeformationClass.dualLineDeformationClass X (dualLineKernelRepresentative X q) (dualLineKernelFrame X q)

theorem dualLineKernelCohomology_rep (q : dualLineClassKernel X)
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (hL : HilbertConstruction.Line.Bundles.LineBundle.classOf L = q.val) :
    dualLineKernelCohomology X q = DeformationClass.dualLineDeformationClass X L e :=
  ReductionFrameIndependence.dualLineDeformationClass_of_iso X L (dualLineKernelRepresentative X q) e (dualLineKernelFrame X q)
    (Quotient.exact ((dualLineKernelRepresentative_class X q).trans hL.symm)).some

theorem dualLineKernelCohomology_of_line (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) :
    dualLineKernelCohomology X (dualLineClassKernelOfLine X L e) = DeformationClass.dualLineDeformationClass X L e :=
  dualLineKernelCohomology_rep X _ L e rfl

theorem dualLineKernelCohomology_one : dualLineKernelCohomology X 1 = 0 :=
  (dualLineKernelCohomology_rep X 1 (HilbertConstruction.Line.Bundles.LineBundle.trivial (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left) rfl).trans (ClassZeroCriterion.dualLineDeformationClass_unit X)

theorem dualLineKernelCohomology_mul (q r : dualLineClassKernel X) :
    dualLineKernelCohomology X (q * r) = dualLineKernelCohomology X q + dualLineKernelCohomology X r := by
  let L := dualLineKernelRepresentative X q
  let K := dualLineKernelRepresentative X r
  let e := dualLineKernelFrame X q
  let d := dualLineKernelFrame X r
  have h : HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor K) = (q * r).val :=
    congrArg₂ (· * ·) (dualLineKernelRepresentative_class X q) (dualLineKernelRepresentative_class X r)
  exact (dualLineKernelCohomology_rep X (q * r) (L.tensor K) (NormalizedDual.TensorFrames.dualTensorReductionFrame X L K e d) h).trans
    (TensorAdditivity.dualLineDeformationClass_tensor X L K e d)

theorem dualLineKernelCohomology_zero_iff (q : dualLineClassKernel X) :
    dualLineKernelCohomology X q = 0 ↔ q = 1 := by
  constructor
  · intro h
    have hL := DeformationTriviality.dualLineDeformationClass_zero_trivial X (dualLineKernelRepresentative X q) (dualLineKernelFrame X q) h
    exact Subtype.ext ((dualLineKernelRepresentative_class X q).symm.trans (Quotient.sound hL))
  · rintro rfl
    exact dualLineKernelCohomology_one X

def dualLineKernelClassHom : dualLineClassKernel X →* Multiplicative (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1) where
  toFun q := Multiplicative.ofAdd (dualLineKernelCohomology X q)
  map_one' := congrArg Multiplicative.ofAdd (dualLineKernelCohomology_one X)
  map_mul' q r := congrArg Multiplicative.ofAdd (dualLineKernelCohomology_mul X q r)

theorem dualLineKernelClassHom_injective : Function.Injective (dualLineKernelClassHom X) := by
  apply (MonoidHom.ker_eq_bot_iff (dualLineKernelClassHom X)).mp
  apply le_antisymm
  · intro q hq
    change dualLineKernelClassHom X q = 1 at hq
    change q = 1
    exact (dualLineKernelCohomology_zero_iff X q).mp (congrArg Multiplicative.toAdd hq)
  · exact bot_le

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel
