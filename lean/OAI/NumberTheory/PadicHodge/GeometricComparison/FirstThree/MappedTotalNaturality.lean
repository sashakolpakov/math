import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalOne

/-! # Mapped Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalNaturality.FirstThreeMappedTotalNaturality

noncomputable section

/-! The original projection onto form degrees zero through two commutes
with transformations of additive row functors before totalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a b
variable (R : Type u) [CommRing R]
  {C : Type a} [Category.{b} C] [Preadditive C] [HasZeroObject C]
  (G H : C ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ) [G.Additive] [H.Additive]
  (α : G ⟶ H) (K : CochainComplex C ℕ)

local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def map : HomologicalComplex₂.total ((G.mapHomologicalComplex (.up ℕ)).obj K) (.up ℕ) ⟶
    HomologicalComplex₂.total ((H.mapHomologicalComplex (.up ℕ)).obj K) (.up ℕ) :=
  HomologicalComplex₂.total.map ((α.mapHomologicalComplex (.up ℕ)).app K) (.up ℕ)

theorem bicomplex : MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap R G K ≫
    (α.mapHomologicalComplex (.up ℕ)).app (ThreeComplex.FirstThreeComplex.complex K) =
      (α.mapHomologicalComplex (.up ℕ)).app K ≫ MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap R H K := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact α.naturality ((ThreeComplex.FirstThreeComplex.projection K).f i)

theorem natural : MappedTotalOne.FirstThreeMappedTotalHOne.map R G K ≫ FirstThreeMappedTotalNaturality.map R G H α (ThreeComplex.FirstThreeComplex.complex K) =
    FirstThreeMappedTotalNaturality.map R G H α K ≫ MappedTotalOne.FirstThreeMappedTotalHOne.map R H K := by
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp (MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap R G K)
    ((α.mapHomologicalComplex (.up ℕ)).app (ThreeComplex.FirstThreeComplex.complex K))).symm.trans
      ((congrArg T.map (bicomplex R G H α K)).trans
        (T.map_comp ((α.mapHomologicalComplex (.up ℕ)).app K) (MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap R H K)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalNaturality.FirstThreeMappedTotalNaturality
