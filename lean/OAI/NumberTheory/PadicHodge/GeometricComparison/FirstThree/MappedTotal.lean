import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexMap

/-! # Mapped Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotal.FirstThreeMappedTotalHodge

noncomputable section

/-! Retaining the first three form degrees preserves each actual
form-degree Hodge image on total H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe a b
variable (R : Type) [CommRing R] {C : Type a} [Category.{b} C] [Abelian C]
  (G : C ⥤ CochainComplex (ModuleCat.{0} R) ℕ) [G.Additive]
  (K : CochainComplex C ℕ) (r : ℤ)

local notation "B" => Functor.obj (Functor.mapHomologicalComplex G (ComplexShape.up ℕ)) K
local notation "B'" => Functor.obj (Functor.mapHomologicalComplex G (ComplexShape.up ℕ)) (OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex K)

def truncatedMap : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r ⟶ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B' r :=
  ComplexMap.HodgeComplexMap.map (MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap.{0, 0, a, b} R G K) r

theorem row_isIso (q : ℕ) (hq : q ≤ 2) : IsIso ((truncatedMap R G K r).f q) := by
  let : IsIso ((MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap.{0, 0, a, b} R G K).f q) :=
    MappedTotalOne.FirstThreeMappedTotalHOne.row_isIso.{0, 0, a, b} R G K q hq
  exact ComplexMap.HodgeComplexMap.component_isIso _ r q

def map := HomologicalComplex₂.total.map (truncatedMap R G K r) (.up ℕ)

theorem quasiIsoAt : QuasiIsoAt (FirstThreeMappedTotalHodge.map R G K r) 1 := by
  let : IsIso ((truncatedMap R G K r).f 0) := row_isIso R G K r 0 (by decide)
  let : IsIso ((truncatedMap R G K r).f 1) := row_isIso R G K r 1 (by decide)
  let : IsIso ((truncatedMap R G K r).f 2) := row_isIso R G K r 2 le_rfl
  exact Module.TotalOneQuasiIso.ModuleTotalHOneQuasiIso.quasiIsoAt (truncatedMap R G K r) inferInstance inferInstance inferInstance

def homologyIso : (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).homology 1 ≅
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B' r) (.up ℕ)).homology 1 := by
  let := quasiIsoAt R G K r
  exact isoOfQuasiIsoAt (FirstThreeMappedTotalHodge.map R G K r) 1

theorem inclusion :
    ModuleCat.ofHom (NaturalTotalImage.NaturalTotalHodgeImage.filtrationMap B 1 r) ≫
      HomologicalComplex.homologyMap (MappedTotalOne.FirstThreeMappedTotalHOne.map.{0, 0, a, b} R G K) 1 =
    (homologyIso R G K r).hom ≫ ModuleCat.ofHom (NaturalTotalImage.NaturalTotalHodgeImage.filtrationMap B' 1 r) := by
  let F := HomologicalComplex₂.totalFunctor (ModuleCat.{0} R) (.up ℕ) (.up ℕ) (.up ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℕ) 1
  have h := congrArg F.map
    (ComplexMap.HodgeComplexMap.inclusion (MappedTotalOne.FirstThreeMappedTotalHOne.bicomplexMap.{0, 0, a, b} R G K) r).symm
  simp only [Functor.map_comp] at h
  have h' := congrArg H.map h
  simp only [Functor.map_comp] at h'
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom h' x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotal.FirstThreeMappedTotalHodge
