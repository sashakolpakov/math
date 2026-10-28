import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentBetti
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseCohomology

/-! # Total -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! The H¹ map of the exact total morphism in IntegralModel. The product and component
comparisons are constructed, and their commuting equation is proved. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
  (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B)

def Components.ComponentAlbaneseData.complexProjectionSum (n : ℕ) :
    (∀ j, Product.bettiQ (D.complexAbelian c j).X n) →ₗ[ℚ]
      Product.bettiQ ((Over.pullback c).obj D.product) n :=
  ∑ j, (Product.bettiPullbackQ ((Over.pullback c).map (Pi.π (fun k => (D.A k).X) j)) n).comp
    (LinearMap.proj j)

theorem Components.ComponentAlbaneseData.complexProjectionSum_comparison (n : ℕ) :
    D.complexProjectionSum c n =
      (ProductDimensions.bettiIso (D.complexProductComparison c) n).toLinearMap.comp
        (Product.ProductBetti.projectionSum (fun j => D.complexAbelian c j) n) := by
  apply LinearMap.ext
  intro x
  change (∑ j, (Product.bettiPullbackQ ((Over.pullback c).map
    (Pi.π (fun k => (D.A k).X) j)) n).comp (LinearMap.proj j)) x =
    Product.bettiPullbackQ (D.complexProductComparison c).hom n
      ((∑ j, (Product.bettiPullbackQ (Pi.π (fun k => (D.complexAbelian c k).X) j) n).comp
        (LinearMap.proj j)) x)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change Product.bettiPullbackQ ((Over.pullback c).map (Pi.π (fun k => (D.A k).X) j)) n (x j) =
    ((Product.bettiPullbackQ (D.complexProductComparison c).hom n).comp
      (Product.bettiPullbackQ (Pi.π (fun k => (D.complexAbelian c k).X) j) n)) (x j)
  rw [← Product.bettiPullbackQ_comp]
  congr 1
  simp [Components.ComponentAlbaneseData.complexProductComparison]

theorem Components.ComponentAlbaneseData.complexProjectionSum_bijective
    [∀ j n, FiniteDimensional ℚ (Product.bettiQ (D.complexAbelian c j).X n)]
    [∀ j, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.complexAbelian c j).X)] :
    Function.Bijective (D.complexProjectionSum c 1) := by
  rw [Components.ComponentAlbaneseData.complexProjectionSum_comparison]
  exact (ProductDimensions.bettiIso (D.complexProductComparison c) 1).bijective.comp
    (ProductDimensions.ProductBetti.projectionSum_bijective (fun j => D.complexAbelian c j))

theorem Components.ComponentAlbaneseData.complexTotalMap_projectionSum (e : (∐ D.S) ≅ T) (n : ℕ) (hn : n ≠ 0) :
    (D.complexComponentBettiEquiv c e n).toLinearMap.comp
      ((Product.bettiPullbackQ (D.totalComplexMap c e) n).comp (D.complexProjectionSum c n)) =
      LinearMap.pi (fun j => (Product.bettiPullbackQ (D.complexMap c j) n).comp
        (LinearMap.proj j)) := by
  have hterm (i j : Fin r) (z : Product.bettiQ (D.complexAbelian c j).X n) :
      Product.bettiPullbackQ ((Over.pullback c).map (Sigma.ι D.S i ≫ e.hom)) n
        (Product.bettiPullbackQ (D.totalComplexMap c e) n
          (Product.bettiPullbackQ ((Over.pullback c).map (Pi.π (fun k => (D.A k).X) j)) n z)) =
        Product.bettiPullbackQ ((Over.pullback c).map (D.coordinateMap i j)) n z := by
    change (((Product.bettiPullbackQ ((Over.pullback c).map (Sigma.ι D.S i ≫ e.hom)) n).comp
      (Product.bettiPullbackQ (D.totalComplexMap c e) n)).comp
        (Product.bettiPullbackQ ((Over.pullback c).map (Pi.π (fun k => (D.A k).X) j)) n)) z = _
    rw [← Product.bettiPullbackQ_comp, ← Product.bettiPullbackQ_comp]
    rw [show ((Over.pullback c).map (Sigma.ι D.S i ≫ e.hom) ≫ D.totalComplexMap c e) ≫
        (Over.pullback c).map (Pi.π (fun k => (D.A k).X) j) =
          (Over.pullback c).map (D.coordinateMap i j) from
      (Category.assoc _ _ _).trans (D.totalComplexMap_coordinate c e i j)]
  apply LinearMap.ext
  intro x
  funext i
  change D.complexComponentBettiEquiv c e n
    (Product.bettiPullbackQ (D.totalComplexMap c e) n (D.complexProjectionSum c n x)) i =
      Product.bettiPullbackQ (D.complexMap c i) n (x i)
  rw [Components.ComponentAlbaneseData.complexComponentBettiEquiv_apply]
  simp only [Components.ComponentAlbaneseData.complexProjectionSum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single i]
  · rw [Components.ComponentAlbaneseData.coordinateMap_self]
    rfl
  · intro j _ hji
    rw [Components.ComponentAlbaneseData.coordinateMap_ne _ i j (Ne.symm hji), Functor.map_one, Product.bettiPullbackQ_one n hn]
    rfl
  · simp

/-- Componentwise H¹ identifications assemble to the map of the actual
total complex morphism. Product and disjoint-union comparisons are proved. -/
theorem Components.ComponentAlbaneseData.totalComplexMap_h1_bijective (e : (∐ D.S) ≅ T)
    [∀ j n, FiniteDimensional ℚ (Product.bettiQ (D.complexAbelian c j).X n)]
    [∀ j, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.complexAbelian c j).X)]
    (hcomponent : ∀ j, Function.Bijective (Product.bettiPullbackQ (D.complexMap c j) 1)) :
    Function.Bijective (Product.bettiPullbackQ (D.totalComplexMap c e) 1) := by
  let R := D.complexComponentBettiEquiv c e 1
  let Q := D.complexProjectionSum c 1
  let P := LinearMap.pi (fun j => (Product.bettiPullbackQ (D.complexMap c j) 1).comp
    (LinearMap.proj j))
  have hQ : Function.Bijective Q := D.complexProjectionSum_bijective c
  have hP : Function.Bijective P := by
    constructor
    · intro x y h
      funext j
      apply (hcomponent j).1
      exact congrFun h j
    · intro y
      choose x hx using fun j => (hcomponent j).2 (y j)
      exact ⟨x, funext hx⟩
  have hfactor (x) : R (Product.bettiPullbackQ (D.totalComplexMap c e) 1 (Q x)) = P x :=
    LinearMap.congr_fun (D.complexTotalMap_projectionSum c e 1 (by decide)) x
  constructor
  · intro x y h
    obtain ⟨u, rfl⟩ := hQ.2 x
    obtain ⟨v, rfl⟩ := hQ.2 y
    exact congrArg Q (hP.1 ((hfactor u).symm.trans ((congrArg R h).trans (hfactor v))))
  · intro y
    obtain ⟨x, hx⟩ := hP.2 (R y)
    exact ⟨Q x, R.injective ((hfactor x).trans hx)⟩

end AlgebraicGeometry.PELModuli.IntegralModel

namespace AlgebraicGeometry.PELModuli.IntegralModel.Total

/-!
HodgeComparison and the actual complex Albanese fibers imply the total H¹ comparison.
No component or product cohomology-comparison hypothesis is added.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem betti_bijective_of_iso_comp {X Y A H : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ A) (g : Y ⟶ H) (eX : X ≅ Y) (eA : A ≅ H)
    (hcompatible : f ≫ eA.hom = eX.hom ≫ g) (n : ℕ)
    (hg : Function.Bijective (Product.bettiPullbackQ g n)) :
    Function.Bijective (Product.bettiPullbackQ f n) := by
  have hf : f = eX.hom ≫ g ≫ eA.inv := by
    rw [← Category.assoc, ← hcompatible, Category.assoc, eA.hom_inv_id, Category.comp_id]
  rw [hf, Product.bettiPullbackQ_comp, Product.bettiPullbackQ_comp]
  exact (ProductDimensions.bettiIso eX n).bijective.comp (hg.comp (ProductDimensions.bettiIso eA.symm n).bijective)

theorem albanese_h1_bijective (hHodgeComparison : AlbaneseCohomology.HodgeComparisonInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
    (ha : Albanese.IsAlbaneseMap X.presentation x₀ A a) :
    Function.Bijective (Product.bettiPullbackQ a 1) := by
  obtain ⟨_, _, e, _, _, he, _, _⟩ :=
    hHodgeComparison X x₀ A a ((AlbaneseCohomology.e08_isAlbanese_iff X x₀ A a).mpr ha)
  change Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom
  rw [← he]
  exact e.bijective

/-- The remaining hypotheses describe the actual complex fibers of a spread,
their algebraic maps, and the Albanese property supplied by Construction. HodgeComparison supplies
the only assumed cohomology theorem. -/
theorem total_h1_of_spread_albanese (hHodgeComparison : AlbaneseCohomology.HodgeComparisonInput)
    {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (e : (∐ D.S) ≅ T)
    (XC : Fin r → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (AC : Fin r → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [∀ j, PathConnectedSpace (XC j).analyticSpace]
    (eX : ∀ j, D.complexSurface c j ≅ (XC j).toOver)
    (eA : ∀ j, (D.complexAbelian c j).X ≅ (AC j).toOver)
    (x₀ : ∀ j, Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ (XC j).toOver)
    (aC : ∀ j, (XC j).toOver ⟶ (AC j).toOver)
    (hcompatible : ∀ j, D.complexMap c j ≫ (eA j).hom = (eX j).hom ≫ aC j)
    (hAlbanese : ∀ j, Albanese.IsAlbaneseMap (XC j).presentation (x₀ j) (AC j) (aC j)) :
    Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (D.totalComplexMap c e)).hom := by
  let : ∀ j n, FiniteDimensional ℚ (Product.bettiQ (AC j).toOver n) := fun j n =>
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite (AC j).variety.presentation n
  let : ∀ j n, FiniteDimensional ℚ (Product.bettiQ (D.complexAbelian c j).X n) :=
    fun j n => ProductDimensions.betti_finite_of_iso (eA j) n
  let : ∀ j, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AC j).toOver) := fun j =>
    AlbaneseTopology.albanesePoints_pathConnected (XC j) (x₀ j) (AC j) (aC j) (hAlbanese j)
  let : ∀ j, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.complexAbelian c j).X) :=
    fun j => ProductGeometry.points_pathConnected_of_iso (eA j)
  apply D.totalComplexMap_h1_bijective c e
  intro j
  exact betti_bijective_of_iso_comp (D.complexMap c j) (aC j) (eX j) (eA j)
    (hcompatible j) 1 (albanese_h1_bijective hHodgeComparison (XC j) (x₀ j) (AC j) (aC j) (hAlbanese j))

/-- ReferenceFamily's actual ball uniformizations discharge the analytic connectedness
needed above. No connectedness of algebraic points is silently assumed. -/
theorem total_h1_of_spread_ball_albanese (hHodgeComparison : AlbaneseCohomology.HodgeComparisonInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (N : ℕ)
    {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (e : (∐ D.S) ≅ T)
    (XC : Fin r → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (AC : Fin r → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (hball : ∀ j, P.IsArithmeticBallUniformized (XC j) N)
    (eX : ∀ j, D.complexSurface c j ≅ (XC j).toOver)
    (eA : ∀ j, (D.complexAbelian c j).X ≅ (AC j).toOver)
    (x₀ : ∀ j, Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ (XC j).toOver)
    (aC : ∀ j, (XC j).toOver ⟶ (AC j).toOver)
    (hcompatible : ∀ j, D.complexMap c j ≫ (eA j).hom = (eX j).hom ≫ aC j)
    (hAlbanese : ∀ j, Albanese.IsAlbaneseMap (XC j).presentation (x₀ j) (AC j) (aC j)) :
    Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (D.totalComplexMap c e)).hom := by
  let : ∀ j, PathConnectedSpace (XC j).analyticSpace := fun j =>
    AlbaneseTopology.BallTopology.pathConnected_of_arithmeticBallUniformized P hP.2.2.2.1 (XC j) N (hball j)
  exact total_h1_of_spread_albanese hHodgeComparison D c e XC AC eX eA x₀ aC hcompatible hAlbanese

end AlgebraicGeometry.PELModuli.IntegralModel.Total

end

end OAI
