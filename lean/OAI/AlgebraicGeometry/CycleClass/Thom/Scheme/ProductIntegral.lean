import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductReduced
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Product Integral -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral.Constructions

noncomputable section

/-! Integrality of genuine products of complex schemes. A product of
nonempty affine opens is integral and dense in the actual fiber product;
reducedness has already been proved on the native full affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductReduced.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem openProduct_denseRange {U V X Y S : Scheme}
    (i : U ⟶ X) (j : V ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    [IsOpenImmersion i] [IsOpenImmersion j] [Nonempty U] [Nonempty V]
    [PreirreducibleSpace X] [PreirreducibleSpace Y] [UniversallyOpen f] [UniversallyOpen g] :
    DenseRange (pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 S)
      (Category.comp_id _) (Category.comp_id _)) := by
  change Dense (Set.range (pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 S)
    (Category.comp_id _) (Category.comp_id _)))
  rw [Scheme.Pullback.range_map]
  have hi := i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i
  have hj := j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  exact (hi.preimage (pullback.fst f g).isOpenMap).inter_of_isOpen_right
    (hj.preimage (pullback.snd f g).isOpenMap)
    (j.isOpenEmbedding.isOpenMap.isOpen_range.preimage (pullback.snd f g).continuous)

theorem schemeProduct_isIntegral (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsIntegral Y.left] : IsIntegral (pullback X.hom Y.hom) := by
  classical
  obtain ⟨i, xi, _⟩ := X.left.affineCover.exists_eq (Classical.choice (inferInstance : Nonempty X.left))
  obtain ⟨j, yj, _⟩ := Y.left.affineCover.exists_eq (Classical.choice (inferInstance : Nonempty Y.left))
  let : Nonempty (X.left.affineCover.X i) := ⟨xi⟩
  let : Nonempty (Y.left.affineCover.X j) := ⟨yj⟩
  let : IsIntegral (X.left.affineCover.X i) := isIntegral_of_isOpenImmersion (X.left.affineCover.f i)
  let : IsIntegral (Y.left.affineCover.X j) := isIntegral_of_isOpenImmersion (Y.left.affineCover.f j)
  let A := Over.mk (X.left.affineCover.f i ≫ X.hom)
  let B := Over.mk (Y.left.affineCover.f j ≫ Y.hom)
  let : IsAffine A.left := Scheme.isAffine_affineCover X.left i
  let : IsAffine B.left := Scheme.isAffine_affineCover Y.left j
  let : LocallyOfFiniteType A.hom := inferInstanceAs (LocallyOfFiniteType (X.left.affineCover.f i ≫ X.hom))
  let : IsIntegral A.left := inferInstanceAs (IsIntegral (X.left.affineCover.X i))
  let : IsIntegral B.left := inferInstanceAs (IsIntegral (Y.left.affineCover.X j))
  let : IsIntegral (pullback A.hom B.hom) := Affine.ProductIs.Constructions.affineProduct_isIntegral A B
  let d : pullback A.hom B.hom ⟶ pullback X.hom Y.hom :=
    pullback.map A.hom B.hom X.hom Y.hom (X.left.affineCover.f i) (Y.left.affineCover.f j)
      (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (Category.comp_id _) (Category.comp_id _)
  have hd : DenseRange d := openProduct_denseRange (X.left.affineCover.f i)
    (Y.left.affineCover.f j) X.hom Y.hom
  have hr : IsIrreducible (Set.range d) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (pullback A.hom B.hom : Scheme)).image d d.continuous.continuousOn
  let : IrreducibleSpace (pullback X.hom Y.hom : Scheme) := by
    rw [irreducibleSpace_def]
    have h := hr.closure
    rw [hd.closure_eq] at h
    exact h
  let : AlgebraicGeometry.IsReduced (pullback X.hom Y.hom) := ProductReduced.Constructions.schemeProduct_isReduced X Y
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral.Constructions
