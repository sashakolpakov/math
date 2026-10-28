import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseActionGluing
import Mathlib.AlgebraicGeometry.Properties

/-! # Action Matching Compatibility -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ActionMatchingCompatibility

noncomputable section

section

/-! Evaluation at the tautological point of a source overlap. This turns
equal restricted actions into equal actual morphisms on that overlap. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace OpenActionOverlap
variable {S : Scheme.{0}} (C : S.OpenCover) {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (i j : C.I₀)

def source : Scheme := pullback (pullback.fst A.scheme.hom (C.f i))
  (pullback.fst A.scheme.hom (C.f j))

def sourceLeft : source C A i j ⟶ pullback A.scheme.hom (C.f i) := pullback.fst _ _
def sourceRight : source C A i j ⟶ pullback A.scheme.hom (C.f j) := pullback.snd _ _

def test : Over S := Over.mk
  ((sourceLeft C A i j ≫ pullback.fst A.scheme.hom (C.f i)) ≫ A.scheme.hom)

instance test_reduced [IsReduced A.scheme.left] : IsReduced (test C A i j).left := by
  have : IsReduced (pullback A.scheme.hom (C.f i)) :=
    isReduced_of_isOpenImmersion (pullback.fst A.scheme.hom (C.f i))
  exact isReduced_of_isOpenImmersion (pullback.fst
    (pullback.fst A.scheme.hom (C.f i)) (pullback.fst A.scheme.hom (C.f j)))

def testLeft : test C A i j ⟶ Over.mk (C.f i) := Over.homMk
  (sourceLeft C A i j ≫ pullback.snd A.scheme.hom (C.f i)) (by
    change (_ ≫ pullback.snd A.scheme.hom (C.f i)) ≫ C.f i = _
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    rfl)

def testRight : test C A i j ⟶ Over.mk (C.f j) := Over.homMk
  (sourceRight C A i j ≫ pullback.snd A.scheme.hom (C.f j)) (by
    change (_ ≫ pullback.snd A.scheme.hom (C.f j)) ≫ C.f j = _
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (fun q => q ≫ A.scheme.hom) (pullback.condition
      (f := pullback.fst A.scheme.hom (C.f i)) (g := pullback.fst A.scheme.hom (C.f j))).symm)

def evaluation : source C A i j ⟶ pullback A.scheme.hom (test C A i j).hom :=
  pullback.lift (sourceLeft C A i j ≫ pullback.fst A.scheme.hom (C.f i))
    (𝟙 _) (Category.id_comp _).symm

theorem evaluation_snd : evaluation C A i j ≫ pullback.snd A.scheme.hom (test C A i j).hom =
    𝟙 (source C A i j) := pullback.lift_snd _ _ _

theorem evaluation_left : evaluation C A i j ≫ EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (testLeft C A i j) =
    sourceLeft C A i j := by
  apply pullback.hom_ext
  · rw [Category.assoc, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_fst]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_snd, ← Category.assoc]
    rw [evaluation_snd, Category.id_comp]
    rfl

theorem evaluation_right : evaluation C A i j ≫ EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (testRight C A i j) =
    sourceRight C A i j := by
  apply pullback.hom_ext
  · rw [Category.assoc, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_fst]
    exact (pullback.lift_fst _ _ _).trans (pullback.condition
      (f := pullback.fst A.scheme.hom (C.f i)) (g := pullback.fst A.scheme.hom (C.f j)))
  · rw [Category.assoc, EndomorphismFamiliesId.EndomorphismFamilies.familyMap_snd, ← Category.assoc]
    rw [evaluation_snd, Category.id_comp]
    rfl

theorem endomorphism_equality (ri : Finite.Actions.GroupEndRing (A.pullback (C.f i)))
    (rj : Finite.Actions.GroupEndRing (A.pullback (C.f j)))
    (h : EndomorphismFamiliesId.EndomorphismFamilies.restrict A (testLeft C A i j) ri = EndomorphismFamiliesId.EndomorphismFamilies.restrict A (testRight C A i j) rj) :
    sourceLeft C A i j ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A (T := Over.mk (C.f i)) ri ≫ pullback.fst A.scheme.hom (C.f i) =
      sourceRight C A i j ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A (T := Over.mk (C.f j)) rj ≫ pullback.fst A.scheme.hom (C.f j) := by
  have he : EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (testLeft C A i j) ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A (T := Over.mk (C.f i)) ri ≫ pullback.fst A.scheme.hom (C.f i) =
      EndomorphismFamiliesId.EndomorphismFamilies.familyMap A (testRight C A i j) ≫ EndomorphismFamiliesId.EndomorphismFamilies.endHom A (T := Over.mk (C.f j)) rj ≫ pullback.fst A.scheme.hom (C.f j) :=
    (EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst A (testLeft C A i j) ri).symm.trans
      ((congrArg (fun r => EndomorphismFamiliesId.EndomorphismFamilies.endHom A r ≫ pullback.fst A.scheme.hom (test C A i j).hom) h).trans
        (EndomorphismFamiliesId.EndomorphismFamilies.restrict_fst A (testRight C A i j) rj))
  have he' := congrArg (fun q => evaluation C A i j ≫ q) he
  simpa only [← Category.assoc, evaluation_left, evaluation_right] using he'

end OpenActionOverlap

end

/-! Matching actual action-functor values imply the literal source-overlap
equations needed for effective gluing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} (C : S.OpenCover) {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    [IsReduced A.scheme.left] {R : Type} [CommRing R]
    (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback (C.f i)))
    (hmatch : ∀ i j (T : Over S) [IsReduced T.left]
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)),
      Integral.ActionScheme.restrictIntegralAction A (ρ i) f = Integral.ActionScheme.restrictIntegralAction A (ρ j) h)

include hmatch in
theorem openAction_matching_compatible (a : R) :
    BaseGroupReflection.OpenBaseMorphismCompatible C (fun i => (ρ i).map a) := by
  intro i j
  let T := OpenActionOverlap.test C A i j
  let f := OpenActionOverlap.testLeft C A i j
  let h := OpenActionOverlap.testRight C A i j
  have he := congrArg
    (fun σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom) => Finite.Actions.ringHomOfIntegralAction _ σ a)
    (hmatch i j T f h)
  exact OpenActionOverlap.endomorphism_equality C A i j
    (Finite.Actions.ringHomOfIntegralAction (A.pullback (C.f i)) (ρ i) a)
    (Finite.Actions.ringHomOfIntegralAction (A.pullback (C.f j)) (ρ j) a) he

include hmatch in
theorem existsUnique_action_of_reduced_matching :
    ∃! σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A, ∀ i, σ.pullback (C.f i) = ρ i :=
  BaseActionGluing.existsUnique_integralAction_of_open_base_cover C A ρ (openAction_matching_compatible C A ρ hmatch)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ActionMatchingCompatibility
