import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficients

/-! # Model Top Cover Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelTopCoverComparison

noncomputable section

/-! The original ordinary cover isomorphism preserves the global
image under the actual native top-form map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose_square {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (u : A ⟶ D) (v : B ⟶ E)
    (c : D ⟶ E) (f : D ⟶ F) (g : E ⟶ F)
    (h : a ≫ v = u ≫ c) (hf : f = c ≫ g) :
    u ≫ f = a ≫ v ≫ g := by rw [hf, ← Category.assoc, ← h, Category.assoc]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficients

omit [Fintype k] [CharP k p] in
theorem mapped_apply {P Q : ModuleCat (Truncated.Witt.Ring p k n)}
    (a : P ⟶ Q) (x : P) :
    (TopCoverCoefficients.second p k).map ((TopCoverCoefficients.first p k n).map a) (ULift.up.{2,1} (ULift.up.{1,0} x)) =
      ULift.up.{2,1} (ULift.up.{1,0} (a x)) := rfl

omit [Fintype k] [CharP k p] in
private theorem apply_comparison {P Q : ModuleCat (Truncated.Witt.Ring p k n)}
    {Z : AddCommGrpCat.{2}} (a : P ⟶ Q)
    (u : (TopCoverCoefficients.second p k).obj ((TopCoverCoefficients.first p k n).obj P) ⟶ Z)
    (v : (TopCoverCoefficients.second p k).obj ((TopCoverCoefficients.first p k n).obj Q) ⟶ Z)
    (h : u = (TopCoverCoefficients.second p k).map ((TopCoverCoefficients.first p k n).map a) ≫ v) (x : P) :
    u (ULift.up.{2,1} (ULift.up.{1,0} x)) = v (ULift.up.{2,1} (ULift.up.{1,0} (a x))) :=
  ConcreteCategory.congr_hom h (ULift.up.{2,1} (ULift.up.{1,0} x))

section Degree
variable (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.left.Opens) (hU : iSup U = ⊤)
  (V : κ → X.left.Opens) (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (T : ν → X.left.Opens)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))

local instance form_qc : (TopCoverCoefficients.form p k n X g).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X g

def globalInput :
    (TopCoverCoefficients.second p k).obj ((TopCoverCoefficients.first p k n).obj
      ((ModuleCech.DimensionBound.complex (Truncated.Witt.Ring p k n) X
        (TopCoverCoefficients.form p k n X g) U).homology g)) ⟶
    (Presheaf.OrderedCechEdge.sections
      (TopCover.target p k n X Y f I)).homology (g+g) :=
  TopCoverCoefficients.inputMap p k n X g U ≫ TopCover.globalMap p k n X Y f hp I g U hU

theorem linear_comparison : globalInput p k n X Y f hp I g U hU =
    (TopCoverCoefficients.second p k).map ((TopCoverCoefficients.first p k n).map
      (ModuleCech.LinearCover.Comparison.comparison (Truncated.Witt.Ring p k n) X
        (TopCoverCoefficients.form p k n X g) U V hV haV T rU rV hT haT g)) ≫
      globalInput p k n X Y f hp I g V hV :=
  compose_square _ _ _ _ _ _
    (TopCoverCoefficients.comparison p k n X g U V hV haV T rU rV hT haT)
    (TopCover.common_refinement p k n X Y f hp I g U hU V hV haV T hT haT rU rV)

theorem linear_apply
    (x : (ModuleCech.DimensionBound.complex (Truncated.Witt.Ring p k n) X
      (TopCoverCoefficients.form p k n X g) U).homology g) :
    globalInput p k n X Y f hp I g U hU (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    globalInput p k n X Y f hp I g V hV
      (ULift.up.{2,1} (ULift.up.{1,0}
        (ModuleCech.LinearCover.Comparison.comparison (Truncated.Witt.Ring p k n) X
          (TopCoverCoefficients.form p k n X g) U V hV haV T rU rV hT haT g x))) :=
  apply_comparison p k n _ _ _
    (linear_comparison p k n X Y f hp I g U hU V hV haV T rU rV hT haT) x

end Degree

variable (r : ℕ) [SmoothOfRelativeDimension (r+1) X.hom]
  {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.left.Opens) (hU : iSup U = ⊤) (haU : ∀ j, IsAffineOpen (U j))
  (V : κ → X.left.Opens) (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (T : ν → X.left.Opens)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  (hT : iSup T = ⊤) (haT : ∀ j, IsAffineOpen (T j))

local instance form_qc_positive : (TopCoverCoefficients.form p k n X (r+1)).IsQuasicoherent :=
  IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent (Truncated.Witt.Ring p k n) X (r+1)

include rU rV hT haT in
theorem cover_apply
    (x : (ModuleCech.DimensionBound.complex (Truncated.Witt.Ring p k n) X
      (TopCoverCoefficients.form p k n X (r+1)) U).homology (r+1)) :
    globalInput p k n X Y f hp I (r+1) U hU (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    globalInput p k n X Y f hp I (r+1) V hV
      (ULift.up.{2,1} (ULift.up.{1,0}
        ((ModuleCech.Cover.Comparison.iso (Truncated.Witt.Ring p k n) X U V
          hU hV haU haV (TopCoverCoefficients.form p k n X (r+1)) r).hom x))) := by
  have h := linear_apply p k n X Y f hp I (r+1) U hU V hV haV T rU rV hT haT x
  have he := ConcreteCategory.congr_hom
    (ModuleCech.LinearCover.Comparison.forget_eq (Truncated.Witt.Ring p k n) X
      (TopCoverCoefficients.form p k n X (r+1)) U V hV haV T rU rV hT haT hU haU r) x
  exact h.trans (congrArg (fun z => globalInput p k n X Y f hp I (r+1) V hV
    (ULift.up.{2,1} (ULift.up.{1,0} z))) he)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelTopCoverComparison
