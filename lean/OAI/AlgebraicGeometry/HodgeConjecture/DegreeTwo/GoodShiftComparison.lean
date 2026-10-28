import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctor
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift

/-! # Good Shift Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftComparison.Constructions

noncomputable section

section

/-! Functorial comparison maps retain actual good shifts and quasi-isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

theorem cochainGoodShiftMap_quasiIso {K L : CochainComplex C ℕ} (f : K ⟶ L)
    [QuasiIso f] (k : ℕ) :
    QuasiIso (HomologicalComplex.truncGE'Map f (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)]
  change QuasiIso (HomologicalComplex.truncGEMap f (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  intro i i' hi
  infer_instance

theorem goodShiftFunctorIso_projection (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ) (k : ℕ)
    (hF : ∀ n, (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n →
      F.PreservesRightHomologyOf (K.sc (k+n))) :
    (GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≫
        (GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).hom =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) := by
  ext n : 1
  exact GoodShiftFunctor.Constructions.goodShiftFunctorDegreeIso_projection F K k hF n

variable {R : Type} [Ring R] {X : TopCat.{0}}
variable {K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ}
variable {S T : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}

theorem sheafComplexLift_postcomp (f : K ⟶ AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex S) (g : S ⟶ T) :
    SheafComplexLift.Constructions.sheafComplexLift (f ≫ ((sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} R)).mapHomologicalComplex (ComplexShape.up ℕ)).map g) =
      SheafComplexLift.Constructions.sheafComplexLift f ≫ g := by
  ext n : 1
  apply Sheaf.hom_ext
  change CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (f.f n ≫ (g.f n).hom) (T.X n).property =
      CategoryTheory.sheafifyLift (Opens.grothendieckTopology X) (f.f n) (S.X n).property ≫
        (g.f n).hom
  rw [CategoryTheory.sheafifyLift_comp]

end

/-! Naturality of the actual cohomology isomorphism for canonical good shifts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]

theorem cochainGoodShiftHomologyIso_naturality {K L : CochainComplex C ℕ}
    (f : K ⟶ L) (k n : ℕ) :
    homologyMap (truncGE'Map f (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n ≫
        (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso L k n).hom =
      (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso K k n).hom ≫ homologyMap f (k+n) := by
  let e := RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k
  have hK : QuasiIsoAt (K.πTruncGE e) (k+n) := K.quasiIsoAt_πTruncGE e (j := n) rfl
  have hL : QuasiIsoAt (L.πTruncGE e) (k+n) := L.quasiIsoAt_πTruncGE e (j := n) rfl
  let eK := (K.truncGE' e).extendHomologyIso e (j := n) (j' := k+n) rfl
  let eL := (L.truncGE' e).extendHomologyIso e (j := n) (j' := k+n) rfl
  change homologyMap (truncGE'Map f e) n ≫
    (eL.inv ≫ (isoOfQuasiIsoAt (L.πTruncGE e) (k+n)).inv) =
      (eK.inv ≫ (isoOfQuasiIsoAt (K.πTruncGE e) (k+n)).inv) ≫ homologyMap f (k+n)
  apply (cancel_epi eK.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc eK.hom, ← extendHomologyIso_hom_naturality]
  simp only [eL, Category.assoc, Iso.hom_inv_id_assoc]
  apply (cancel_epi (homologyMap (K.πTruncGE e) (k+n))).mp
  rw [← Category.assoc, ← homologyMap_comp]
  change homologyMap (K.πTruncGE e ≫ truncGEMap f e) (k+n) ≫
      (isoOfQuasiIsoAt (L.πTruncGE e) (k+n)).inv = _
  rw [πTruncGE_naturality, homologyMap_comp, Category.assoc,
    isoOfQuasiIsoAt_hom_inv_id, Category.comp_id,
    isoOfQuasiIsoAt_hom_inv_id_assoc]

theorem cochainGoodShiftQuasiIso_homology_inverse {K L : CochainComplex C ℕ}
    (f : K ⟶ L) [QuasiIso f] (k n : ℕ) :
    homologyMap (truncGE'Map f (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n ≫
        (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso L k n).hom ≫ (isoOfQuasiIsoAt f (k+n)).inv =
      (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso K k n).hom := by
  rw [← Category.assoc, cochainGoodShiftHomologyIso_naturality, Category.assoc,
    isoOfQuasiIsoAt_hom_inv_id, Category.comp_id]

def cochainGoodShiftComparisonIso {K L B : CochainComplex C ℕ}
    (f : K ⟶ L) [QuasiIso f] (k n : ℕ)
    (e : L.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≅ B) : B.homology n ≅ K.homology (k+n) :=
  (homologyFunctor C (ComplexShape.up ℕ) n).mapIso e.symm ≪≫
    GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso L k n ≪≫ (isoOfQuasiIsoAt f (k+n)).symm

theorem cochainGoodShiftComparisonIso_transport {A K L B : CochainComplex C ℕ}
    (f : K ⟶ L) [QuasiIso f] (k n : ℕ)
    (e : L.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≅ B)
    (g : A ⟶ K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) :
    homologyMap (g ≫ truncGE'Map f (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≫ e.hom) n ≫
        (cochainGoodShiftComparisonIso f k n e).hom =
      homologyMap g n ≫ (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso K k n).hom := by
  simp only [cochainGoodShiftComparisonIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, homologyFunctor_map, homologyMap_comp, Category.assoc]
  rw [← Category.assoc (homologyMap e.hom n), ← homologyMap_comp,
    Iso.hom_inv_id, homologyMap_id, Category.id_comp]
  rw [cochainGoodShiftQuasiIso_homology_inverse]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftComparison.Constructions
