import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralFirstThreeSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation

/-! # Affine Model Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame

noncomputable section

/-! Every actual affine open of a smooth finite-Witt-level model gives
a native frame on the original crystalline site of its special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Witt.reduction p k n))))
  (U : X.left.Opens) (hU : IsAffineOpen U)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n

abbrev sourceRing := Γ(X.left, U)
abbrev targetRing := Γ(Y.left, f ⁻¹ᵁ U)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X U
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f U

local instance residueBase : Algebra S k := (Witt.reduction p k n).toAlgebra
local instance sourceAlgebra : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U
local instance targetAlgebra : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ U)

omit [Fintype k] [CharP k p] in
include hU in
theorem source_smooth : Algebra.Smooth S A :=
  GeometricComparison.Smooth.IntegralFirstThreeSections.SmoothIntegralFirstThreeSections.algebra_smooth S X U hU

def reduction : A →+* C := (f.app U).hom

omit [Smooth X.hom] in
include hp hU in
theorem reduction_surjective : Function.Surjective (reduction p k n X Y f U) :=
  AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.surjective S k X Y f hp U hU (Witt.reduction_surjective p k n)

omit [Smooth X.hom] in
include hp hU in
theorem reduction_kernel : RingHom.ker (reduction p k n X Y f U) = Ideal.span {(p : A)} := by
  have hker : RingHom.ker (Witt.reduction p k n) = Ideal.span {(p : S)} := by
    rw [Witt.reduction_kernel]
    change (Ideal.span {(p : W)}).map (Witt.quotient p k n) = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h := AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.kernel_principal S k X Y f hp U hU
    (Witt.reduction_surjective p k n) (p : S) hker
  simpa only [reduction, sourceRing, map_natCast] using h

omit [Smooth X.hom] in
include hp hU in
theorem reduction_base (w : W) :
    reduction p k n X Y f U (algebraMap S A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w) :=
  AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.base S k X Y f hp U hU (Witt.quotient p k n w)

omit [Smooth X.hom] in
include hp hU in
theorem residue_affine : IsAffineOpen (f ⁻¹ᵁ U) := by
  let : IsAffineHom f := MorphismProperty.of_isPullback hp.flip
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom (Witt.reduction p k n))))
  exact hU.preimage f

def chart : Spec (CommRingCat.of C) ⟶ Y.left := (residue_affine p k n X Y f hp U hU).fromSpec

instance chart_open : IsOpenImmersion (chart p k n X Y f hp U hU) :=
  IsAffineOpen.isOpenImmersion_fromSpec (residue_affine p k n X Y f hp U hU)

omit [Smooth X.hom] in
theorem chart_over : chart p k n X Y f hp U hU ≫ Y.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k C)) :=
  AffineOpen.SectionBase.overBase k Y (f ⁻¹ᵁ U) (residue_affine p k n X Y f hp U hU)

def localFrame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n := by
  letI := source_smooth p k n X U hU
  exact SmoothFrame.boundedFrame p A C (reduction p k n X Y f U)
    (reduction_surjective p k n X Y f hp U hU) (reduction_kernel p k n X Y f hp U hU) k n
    (reduction_base p k n X Y f hp U hU)

def frame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n :=
  (BoundedOpen.Equivalence.postcompose (chart p k n X Y f hp U hU)
    (Crystalline.OpenPresentation.overWitt p k C Y (chart p k n X Y f hp U hU)
      (chart_over p k n X Y f hp U hU)) n).obj
    (localFrame p k n X Y f hp U hU)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame
