import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.FamilyHomGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.LawsBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GroupObjectClassifier

/-! # Open Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.OpenDescent.FamilyGroupOperations

noncomputable section

/-! Actual commutative group operations descend on a locally directed
open cover. All six group laws are reflected by the native pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {X : Over S}

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.laws_of_openCover (D : Operations.FamilyGroupOperations X) (C : S.OpenCover.{u})
    (h : ∀ i, (D.baseChange (C.f i)).Laws) : D.Laws := by
  have hm i : D.MappedLaws (Over.pullback (C.f i)) :=
    (D.map_laws_iff (Over.pullback (C.f i))).mp (h i)
  exact ⟨HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hm i).one_mul),
    HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hm i).mul_one),
    HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hm i).mul_assoc),
    HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hm i).left_inv),
    HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hm i).right_inv),
    HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C _ _ (fun i => (hm i).mul_comm)⟩

variable (C : S.OpenCover.{u}) [Category C.I₀] [C.LocallyDirected]
  (D : ∀ i, Operations.FamilyGroupOperations ((Over.pullback (C.f i)).obj X))
  (hD : ∀ {i j : C.I₀} (f : i ⟶ j),
    (D j).geometricBaseChange (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) = D i)

private abbrev data (i : C.I₀) :=
  (Intrinsic.FamilyOperationData.familyOperationDataEquiv X (Directed.FamilyHomGluing.DirectedFamilyHomGluing.test C i)).symm (D i)

include hD in
private theorem data_natural {i j : C.I₀} (f : i ⟶ j) :
    ((Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) (data C D j).1.1,
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) (data C D j).1.2),
      Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f ≫ (data C D j).2) = data C D i := by
  apply (Intrinsic.FamilyOperationData.familyOperationDataEquiv X (Directed.FamilyHomGluing.DirectedFamilyHomGluing.test C i)).injective
  have hn := Geometric.GeometricFamilyGroupOperations.familyOperationData_geometricBaseChange (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f)
    (data C D j).1.1 (data C D j).1.2 (data C D j).2
  rw [Equiv.apply_symm_apply] at hn
  exact hn.symm.trans ((hD f).trans (Equiv.apply_symm_apply _ _).symm)

include hD in
private theorem mul_natural {i j : C.I₀} (f : i ⟶ j) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) (data C D j).1.1 =
      (data C D i).1.1 := congrArg (fun x => x.1.1) (data_natural C D hD f)

include hD in
private theorem inv_natural {i j : C.I₀} (f : i ⟶ j) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) (data C D j).1.2 =
      (data C D i).1.2 := congrArg (fun x => x.1.2) (data_natural C D hD f)

include hD in
private theorem unit_natural {i j : C.I₀} (f : i ⟶ j) :
    C.trans f ≫ (data C D j).2.left = (data C D i).2.left :=
  congrArg (fun x => x.2.left) (data_natural C D hD f)

private def descendedUnit : 𝟙_ (Over S) ⟶ X :=
  Over.homMk
    (C.glueMorphismsOfLocallyDirected (fun i => (data C D i).2.left)
      (unit_natural C D hD)) (by
        apply C.hom_ext
        intro i
        rw [← Category.assoc, C.map_glueMorphismsOfLocallyDirected, (data C D i).2.w]
        change C.f i = C.f i ≫ 𝟙 S
        exact (Category.comp_id _).symm)

/-- The three actual scheme maps obtained by open-cover descent. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.descend : Operations.FamilyGroupOperations X where
  unit := descendedUnit C D hD
  mul := Directed.FamilyHomGluing.DirectedFamilyHomGluing.glue C (X ⊗ X) X
    (fun i => (data C D i).1.1) (mul_natural C D hD)
  inv := Directed.FamilyHomGluing.DirectedFamilyHomGluing.glue C X X
    (fun i => (data C D i).1.2) (inv_natural C D hD)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.descend_baseChange (i : C.I₀) :
    (Operations.FamilyGroupOperations.descend C D hD).baseChange (C.f i) = D i := by
  have he := (Intrinsic.FamilyOperationData.familyOperationDataEquiv X (Directed.FamilyHomGluing.DirectedFamilyHomGluing.test C i)).apply_symm_apply (D i)
  apply Operations.FamilyGroupOperations.ext
  · have heU := congrArg Operations.FamilyGroupOperations.unit he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((Functor.LaxMonoidal.ε (Over.pullback (C.f i))).left ≫
        ((Over.pullback (C.f i)).map (descendedUnit C D hD)).left) ≫
          pullback.fst X.hom (C.f i) = (D i).unit.left ≫ pullback.fst X.hom (C.f i)
      rw [Category.assoc, Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc]
      change ((Functor.LaxMonoidal.ε (Over.pullback (C.f i))).left ≫
        pullback.fst (𝟙 S) (C.f i)) ≫ (descendedUnit C D hD).left = _
      rw [Family.PointSectionNaturality.pullbackUnitComparison_fst]
      have hg : C.f i ≫ (descendedUnit C D hD).left = (data C D i).2.left :=
        C.map_glueMorphismsOfLocallyDirected (fun i => (data C D i).2.left)
          (unit_natural C D hD) i
      exact hg.trans ((Family.PointSectionNaturality.familyPointSection_fst X (data C D i).2).symm.trans
        (congrArg (fun q => q.left ≫ pullback.fst X.hom (C.f i)) heU))
    · exact ((Operations.FamilyGroupOperations.descend C D hD).baseChange (C.f i)).unit.w.trans (D i).unit.w.symm
  · have hm := Directed.FamilyHomGluing.DirectedFamilyHomGluing.glue_pullback C (X ⊗ X) X
      (fun i => (data C D i).1.1) (mul_natural C D hD) i
    change (Functor.LaxMonoidal.μ (Over.pullback (C.f i)) X X) ≫
      (Over.pullback (C.f i)).map (Operations.FamilyGroupOperations.descend C D hD).mul = (D i).mul
    rw [show (Over.pullback (C.f i)).map (Operations.FamilyGroupOperations.descend C D hD).mul = (data C D i).1.1 from hm]
    exact congrArg Operations.FamilyGroupOperations.mul he
  · exact Directed.FamilyHomGluing.DirectedFamilyHomGluing.glue_pullback C X X
      (fun i => (data C D i).1.2) (inv_natural C D hD) i

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.descend_laws (h : ∀ i, (D i).Laws) : (Operations.FamilyGroupOperations.descend C D hD).Laws := by
  apply Operations.FamilyGroupOperations.laws_of_openCover _ C
  intro i
  rw [Operations.FamilyGroupOperations.descend_baseChange C D hD i]
  exact h i

/-- The resulting genuine commutative group object. -/
@[instance_reducible] def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.descendGroup (h : ∀ i, (D i).Laws) : GrpObj X :=
  (Operations.FamilyGroupOperations.descend C D hD).groupObj (Operations.FamilyGroupOperations.descend_laws C D hD h)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.descendGroup_commutative (h : ∀ i, (D i).Laws) :
    letI := Operations.FamilyGroupOperations.descendGroup C D hD h
    IsCommMonObj X :=
  (Operations.FamilyGroupOperations.descend C D hD).groupObj_comm (Operations.FamilyGroupOperations.descend_laws C D hD h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.OpenDescent.FamilyGroupOperations
