import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.RestrictionInjectives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.EmptyFrame

/-! # Derived Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedEvaluation.FramedCrystallineDerivedEvaluation

noncomputable section

/-!
# Positive derived evaluations on the framed crystalline site

Exact restriction preserves injectives, so a native injective resolution
restricts to an injective resolution on the framed site. Its evaluation
at a framed object is the original evaluation at the underlying native
object. Native Čech acyclicity thus proves framed derived vanishing.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness.FramedCrystallineSheafExactness.restriction p k B σ a V

def evaluation (Q : Category.FramedCrystallineCategory.Object p k B σ a) : Sheaf K V ⥤ V :=
  sheafToPresheaf K V ⋙ (CategoryTheory.evaluation _ _).obj (op Q)

instance evaluation_additive (Q : Category.FramedCrystallineCategory.Object p k B σ a) :
    (FramedCrystallineDerivedEvaluation.evaluation p k B σ a Q).Additive := by
  dsimp [FramedCrystallineDerivedEvaluation.evaluation]
  infer_instance

instance evaluation_preservesLimits (Q : Category.FramedCrystallineCategory.Object p k B σ a) :
    PreservesLimits (FramedCrystallineDerivedEvaluation.evaluation p k B σ a Q) := by
  dsimp [FramedCrystallineDerivedEvaluation.evaluation]
  infer_instance

theorem restriction_isZero (F : Sheaf J V) (hF : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X F)
    (Q : Category.FramedCrystallineCategory.Object p k B σ a) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((FramedCrystallineDerivedEvaluation.evaluation p k B σ a Q).rightDerived n).obj ((U).obj F)) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    let I : InjectiveResolution F := injectiveResolution F
    let I' : InjectiveResolution ((U).obj F) := ExactInjective.ExactInjectiveResolution.map U I
    have he : (((FramedCrystallineDerivedEvaluation.evaluation p k B σ a Q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I'.cocomplex).ExactAt (n + 1) :=
      DerivedVanishing.CrystallineDerivedVanishing.evaluated_exactAt p k X F hF I Q.base n
    exact he.isZero_homology.of_iso (I'.isoRightDerivedObj (FramedCrystallineDerivedEvaluation.evaluation p k B σ a Q) (n + 1))

theorem structure_isZero (Q : Category.FramedCrystallineCategory.Object p k B σ a)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (((FramedCrystallineDerivedEvaluation.evaluation p k B σ a Q).rightDerived n).obj
      ((U).obj (Site.structureSheaf p k X))) :=
  restriction_isZero p k B σ a _ (EmptyFrame.CrystallineEmptyFrame.structure_acyclic p k B) Q n hn

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedEvaluation.FramedCrystallineDerivedEvaluation
