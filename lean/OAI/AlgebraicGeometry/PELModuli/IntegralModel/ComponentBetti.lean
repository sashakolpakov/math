import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ProductDimensions
import OAI.AlgebraicTopology.Cohomology.Singular.FiniteCoproduct

/-! # Component Betti -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual component restrictions give the Betti decomposition after
base change. This uses the proved disjoint open cover on schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicTopology.Cohomology.Singular.FiniteCoproduct

variable {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
  (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (e : (∐ D.S) ≅ T)

def Components.ComponentAlbaneseData.complexComponentPointIso :
    TopCat.of (Σ i, Betti.Scheme.schemePointSpace (D.complexSurface c i)) ≅
      Betti.Scheme.schemePointSpace ((Over.pullback c).obj T) := by
  let : ∀ i, IsOpenImmersion (Sigma.ι D.S i ≫ e.hom).left :=
    fun i => Coproduct.decomposition_inclusion_open D.S e i
  let : ∀ i, IsOpenImmersion ((Over.pullback c).map (Sigma.ι D.S i ≫ e.hom)).left :=
    fun i => Coproduct.baseChange_inclusion_open c _
  exact TopCat.isoOfHomeo
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph ((Over.pullback c).obj T)
      (fun i => D.complexSurface c i)
      (fun i => (Over.pullback c).map (Sigma.ι D.S i ≫ e.hom))
      (Coproduct.baseChange_decomposition_cover D.S c e)
      (Coproduct.baseChange_decomposition_disjoint D.S c e))

@[reassoc (attr := simp)] theorem Components.ComponentAlbaneseData.complexComponentPointIso_ι (i : Fin r) :
    TopCat.sigmaι (fun i => Betti.Scheme.schemePointSpace (D.complexSurface c i)) i ≫
      (D.complexComponentPointIso c e).hom =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map ((Over.pullback c).map (Sigma.ι D.S i ≫ e.hom)) := by
  apply TopCat.ext
  intro p
  rfl

def Components.ComponentAlbaneseData.complexComponentBettiEquiv (n : ℕ) :
    Product.bettiQ ((Over.pullback c).obj T) n ≃ₗ[ℚ]
      (∀ i, Product.bettiQ (D.complexSurface c i) n) :=
  ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℚ ℚ) n).mapIso
    (D.complexComponentPointIso c e).op).toLinearEquiv.trans
      (AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv (fun i => Betti.Scheme.schemePointSpace (D.complexSurface c i))
        (ModuleCat.of ℚ ℚ) n)

theorem Components.ComponentAlbaneseData.complexComponentBettiEquiv_apply (n : ℕ)
    (x : Product.bettiQ ((Over.pullback c).obj T) n) (i : Fin r) :
    D.complexComponentBettiEquiv c e n x i =
      Product.bettiPullbackQ ((Over.pullback c).map (Sigma.ι D.S i ≫ e.hom)) n x := by
  change AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv (fun i => Betti.Scheme.schemePointSpace (D.complexSurface c i))
    (ModuleCat.of ℚ ℚ) n
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (D.complexComponentPointIso c e).hom n x) i = _
  rw [AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv_apply]
  have hp := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ)
    (TopCat.sigmaι (fun i => Betti.Scheme.schemePointSpace (D.complexSurface c i)) i)
    (D.complexComponentPointIso c e).hom n
  rw [Components.ComponentAlbaneseData.complexComponentPointIso_ι] at hp
  exact (ConcreteCategory.congr_hom hp x).symm

theorem Components.ComponentAlbaneseData.totalComplexMap_coordinate (i j : Fin r) :
    (Over.pullback c).map (Sigma.ι D.S i ≫ e.hom) ≫
      D.totalComplexMap c e ≫
      (Over.pullback c).map (Pi.π (fun k => (D.A k).X) j) =
      (Over.pullback c).map (D.coordinateMap i j) := by
  simp only [Components.ComponentAlbaneseData.totalComplexMap, ← Functor.map_comp]
  congr 1
  simpa only [Category.assoc] using D.totalMap_coordinate e i j

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
