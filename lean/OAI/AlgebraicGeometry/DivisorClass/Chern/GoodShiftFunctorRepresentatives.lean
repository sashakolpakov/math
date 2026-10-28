import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctor
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives

/-! # Good Shift Functor Representatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GoodShiftFunctorRepresentatives

noncomputable section

/-! The good-shift comparison retains actual cocycle representatives under the original boundary projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type*} [Category C] [Abelian C] {R : Type} [Ring R]
variable (F : C ⥤ ModuleCat.{0} R) [F.Additive] (K : CochainComplex C ℕ) (k : ℕ)
variable (hF : ∀ n, (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n →
  F.PreservesRightHomologyOf (K.sc (k+n)))

def goodShiftFunctorCocycle (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (k+n)) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F (K.truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).hom n
    (HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) k n c)

theorem goodShiftFunctorCocycle_value (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (k+n)) :
    (goodShiftFunctorCocycle F K k hF n c).val =
      F.map ((K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n) c.val := by
  exact ConcreteCategory.congr_hom (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorDegreeIso_projection F K k hF n) c.val

def goodShiftFunctorHomologyIso (n : ℕ) :
    (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F (K.truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))).homology n ≅
      (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K).homology (k+n) :=
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).symm ≪≫
    HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) k n

theorem goodShiftFunctorHomologyIso_class (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (k+n)) :
    (goodShiftFunctorHomologyIso F K k hF n).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (goodShiftFunctorCocycle F K k hF n c)) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (k+n) c := by
  rw [goodShiftFunctorHomologyIso]
  change (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) k n).hom
    (HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).inv n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (goodShiftFunctorCocycle F K k hF n c))) = _
  unfold goodShiftFunctorCocycle
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  have he : HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).hom n ≫
      HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).inv n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id, HomologicalComplex.homologyMap_id]
  have hv := ConcreteCategory.congr_hom he
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) k n c))
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hv
  rw [hv]
  exact HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftHomologyIso_class (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) k n c

theorem goodShiftFunctorHomologyIso_image_class
    {A : CochainComplex C ℕ} (g : A ⟶ K.restriction (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))
    (n : ℕ) (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F A) n)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (k+n))
    (hc : F.map (g.f n) b.val = c.val) :
    (goodShiftFunctorHomologyIso F K k hF n).hom
      (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (g ≫ K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) n (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n b)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (k+n) c := by
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  have h : AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (g ≫ K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) n b =
      goodShiftFunctorCocycle F K k hF n c := by
    apply Subtype.ext
    rw [goodShiftFunctorCocycle_value]
    change F.map (g.f n ≫ (K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n) b.val = _
    rw [Functor.map_comp, ConcreteCategory.comp_apply, hc]
  rw [h]
  exact goodShiftFunctorHomologyIso_class F K k hF n c

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GoodShiftFunctorRepresentatives
