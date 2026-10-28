import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Total
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
import OAI.AlgebraicGeometry.AbelianVariety.PowerImage
import OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible

/-! # Component Albanese Betti -/

namespace OAI.RepresentationTheory.Theta.Geometric.ComponentAlbaneseBetti

noncomputable section

/-! The actual total IntegralModel Betti isomorphism implies the individual
component Albanese isomorphisms, through the proved product and component
decompositions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
open scoped _root_.CategoryTheory.MonObj

theorem diagonalLinear_bijective_component {k I : Type} [Field k] [DecidableEq I]
    {V W : I → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module k (W j)] (f : ∀ j, V j →ₗ[k] W j)
    (hf : Function.Bijective (LinearMap.pi (fun j => (f j).comp (LinearMap.proj j))))
    (j : I) : Function.Bijective (f j) := by
  constructor
  · intro a b hab
    have h : (LinearMap.pi (fun j => (f j).comp (LinearMap.proj j))) (Pi.single j a) =
        (LinearMap.pi (fun j => (f j).comp (LinearMap.proj j))) (Pi.single j b) := by
      funext t
      by_cases ht : t = j
      · subst t
        simpa using hab
      · simp [Pi.single_eq_of_ne ht]
    simpa using congrFun (hf.1 h) j
  · intro b
    obtain ⟨v, hv⟩ := hf.2 (Pi.single j b)
    exact ⟨v j, by simpa using congrFun hv j⟩

namespace SphericalPELAlbaneseData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

include hg in
theorem complexComponentAlbanese_betti_bijective (j : Fin D.componentCount) :
    Function.Bijective (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ (D.components.complexMap D.complexPoint j) 1) := by
  let : IsIso D.componentAssembly := hg.decomposition
  let : ∀ j n, FiniteDimensional ℚ (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiQ (D.components.complexAbelian D.complexPoint j).X n) :=
    fun j n => AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite
      (D.actualComplexComponentAlbaneseVariety hg j).variety.presentation n
  let : ∀ j, PathConnectedSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.components.complexAbelian D.complexPoint j).X) := by
    intro j
    let A := D.actualComplexComponentAlbaneseVariety hg j
    let : ConnectedSpace A.variety.analyticSpace := AlgebraicGeometry.AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
    let : LocallyPathConnectedSpace A.variety.analyticSpace :=
      AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
    change PathConnectedSpace A.variety.analyticSpace
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  let R := D.components.complexComponentBettiEquiv D.complexPoint (asIso D.componentAssembly) 1
  let Q := D.components.complexProjectionSum D.complexPoint 1
  have hb : Function.Bijective
      (R.toLinearMap.comp ((AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ
        (D.components.totalComplexMap D.complexPoint (asIso D.componentAssembly)) 1).comp Q)) :=
    R.bijective.comp (hg.betti.comp (D.components.complexProjectionSum_bijective D.complexPoint))
  have he := D.components.complexTotalMap_projectionSum D.complexPoint
    (asIso D.componentAssembly) 1 (by decide)
  change R.toLinearMap.comp ((AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ
    (D.components.totalComplexMap D.complexPoint (asIso D.componentAssembly)) 1).comp Q) = _ at he
  rw [he] at hb
  exact diagonalLinear_bijective_component _ hb j

end SphericalPELAlbaneseData

end

end OAI.RepresentationTheory.Theta.Geometric.ComponentAlbaneseBetti
