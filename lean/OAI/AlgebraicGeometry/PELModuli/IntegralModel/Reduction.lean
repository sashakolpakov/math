import OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Lean.Util.CollectAxioms

/-! # Reduction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction

noncomputable section

/-!
The reduction used by IntegralModel is the actual subscheme cut out by the nilradical.
Its reduced-test-scheme universal property is proved from algebraic
factorization through closed immersions. No classifying property is added
as a field of a model.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

abbrev reduction {B : Scheme.{u}} (X : Over B) : Over B :=
  Over.mk (X.left.nilradical.subschemeι ≫ X.hom)

abbrev reductionι {B : Scheme.{u}} (X : Over B) : reduction X ⟶ X :=
  Over.homMk X.left.nilradical.subschemeι rfl

instance reduction_closed {B : Scheme.{u}} (X : Over B) :
    IsClosedImmersion (reductionι X).left :=
  inferInstanceAs (IsClosedImmersion X.left.nilradical.subschemeι)

instance reduction_mono {B : Scheme.{u}} (X : Over B) : Mono (reductionι X) :=
  Over.mono_of_mono_left _

@[simp] theorem reduction_range {B : Scheme.{u}} (X : Over B) :
    Set.range (reductionι X).left = Set.univ := by
  change Set.range X.left.nilradical.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  rfl

instance reduction_reduced {B : Scheme.{u}} (X : Over B) :
    IsReduced (reduction X).left := by
  let I := X.left.nilradical
  change IsReduced I.subscheme
  apply (IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).mpr
  intro U
  change X.left.affineOpens at U
  change IsReduced (Spec (.of (Γ(X.left, U) ⧸ I.ideal U)))
  apply (affine_isReduced_iff _).mpr
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  change (Ideal.radical (⊥ : Ideal Γ(X.left, U))).IsRadical
  exact Ideal.radical_isRadical _

def factorToReduction {B : Scheme.{u}} {Y X : Over B} [IsReduced Y.left]
    (f : Y ⟶ X) : Y ⟶ reduction X :=
  Over.homMk
    (Albanese.Construction.ReducedFactor.factorThroughClosed (reductionι X).left f.left (by
      rw [reduction_range]
      exact Set.subset_univ _)) (by
      change Albanese.Construction.ReducedFactor.factorThroughClosed _ _ _ ≫
        ((reductionι X).left ≫ X.hom) = Y.hom
      rw [← Category.assoc, Albanese.Construction.ReducedFactor.factorThroughClosed_comp]
      exact f.w)

@[reassoc (attr := simp)] theorem factorToReduction_ι
    {B : Scheme.{u}} {Y X : Over B} [IsReduced Y.left] (f : Y ⟶ X) :
    factorToReduction f ≫ reductionι X = f := by
  ext1
  exact Albanese.Construction.ReducedFactor.factorThroughClosed_comp (reductionι X).left f.left
    (by rw [reduction_range]; exact Set.subset_univ _)

/-- Passing to the reduction preserves all morphisms from reduced test schemes. -/
def reductionHomEquiv {B : Scheme.{u}} (Y X : Over B) [IsReduced Y.left] :
    (Y ⟶ reduction X) ≃ (Y ⟶ X) where
  toFun f := f ≫ reductionι X
  invFun f := factorToReduction f
  left_inv f := by
    apply (cancel_mono (reductionι X)).mp
    exact factorToReduction_ι _
  right_inv f := factorToReduction_ι f

/-- Naturality makes this the reduced-test-scheme moduli comparison. -/
theorem reductionHomEquiv_naturality
    {B : Scheme.{u}} {Y Z X : Over B} [IsReduced Y.left] [IsReduced Z.left]
    (f : Y ⟶ Z) (g : Z ⟶ reduction X) :
    reductionHomEquiv Y X (f ≫ g) = f ≫ reductionHomEquiv Z X g := by
  change (f ≫ g) ≫ reductionι X = f ≫ g ≫ reductionι X
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
