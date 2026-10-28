import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift

/-! # Good Shift Functor Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctorNaturality.Constructions

noncomputable section

/-! The actual good-shift comparison is natural in the additive section functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
variable (K : CochainComplex C ℕ) (k : ℕ)
variable (hF : ∀ n, (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n → F.PreservesRightHomologyOf (K.sc (k+n)))
variable (hG : ∀ n, (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n → G.PreservesRightHomologyOf (K.sc (k+n)))

theorem goodShiftFunctorIso_functor_naturality :
    HomologicalComplex.truncGE'Map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K)
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≫ (GoodShiftFunctor.Constructions.goodShiftFunctorIso G K k hG).hom =
      (GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).hom ≫
        (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
          (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) := by
  ext n : 1
  apply (cancel_epi (((GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE'
    (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n)).mp
  have hp := congrArg (fun q => q.f n)
    (HomologicalComplex.restrictionToTruncGE'_naturality
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))
  change ((GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n ≫
      (HomologicalComplex.truncGE'Map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K)
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n =
    α.app (K.X (k+n)) ≫ ((GoodShiftFunctor.Constructions.functorCochainComplex G K).restrictionToTruncGE'
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n at hp
  change ((GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n ≫
      ((HomologicalComplex.truncGE'Map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K)
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n ≫ (GoodShiftFunctor.Constructions.goodShiftFunctorDegreeIso G K k hG n).hom) =
    ((GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n ≫
      ((GoodShiftFunctor.Constructions.goodShiftFunctorDegreeIso F K k hF n).hom ≫ α.app ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).X n))
  rw [← Category.assoc, hp, Category.assoc, GoodShiftFunctor.Constructions.goodShiftFunctorDegreeIso_projection,
    ← Category.assoc, GoodShiftFunctor.Constructions.goodShiftFunctorDegreeIso_projection]
  exact (α.naturality ((K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n)).symm

theorem goodShiftFunctorCohomologyIso_functor_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) n ≫
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).mapIso
        (GoodShiftFunctor.Constructions.goodShiftFunctorIso G K k hG).symm ≪≫ GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex G K) k n).hom =
    ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).mapIso
        (GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).symm ≪≫ GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex F K) k n).hom ≫
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) (k+n) := by
  let t := HomologicalComplex.truncGE'Map
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)
  have hi : (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
      (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) ≫ (GoodShiftFunctor.Constructions.goodShiftFunctorIso G K k hG).inv =
    (GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).inv ≫ t := by
    apply (cancel_epi (GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).hom).mp
    rw [← Category.assoc, ← goodShiftFunctorIso_functor_naturality F G α K k hF hG,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  change HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
      (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) n ≫
      (HomologicalComplex.homologyMap (GoodShiftFunctor.Constructions.goodShiftFunctorIso G K k hG).inv n ≫
        (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex G K) k n).hom) =
    (HomologicalComplex.homologyMap (GoodShiftFunctor.Constructions.goodShiftFunctorIso F K k hF).inv n ≫
      (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex F K) k n).hom) ≫
      HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) (k+n)
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, hi,
    HomologicalComplex.homologyMap_comp, Category.assoc]
  have hn := GoodShiftComparison.Constructions.cochainGoodShiftHomologyIso_naturality
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) k n
  change HomologicalComplex.homologyMap t n ≫
      (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (GoodShiftFunctor.Constructions.functorCochainComplex G K) k n).hom = _ at hn
  rw [hn, ← Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctorNaturality.Constructions
