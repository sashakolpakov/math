import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionProjectionExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseTransitionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProductHomologyKernel

/-! # Restriction Joint Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RestrictionJointKernel

noncomputable section

/-! When the original inverse-limit inclusion is injective on cohomology, the actual bounded crystalline restriction maps have zero common kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedProductCohomology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := p) (J := J) (δ := δ) f

def sourceEquiv (i : ℕ) : (S).X₁.homology i ≃ₗ[R]
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i :=
  (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R (S).X₁ i).trans
    (BoundedResolution.Comparison.homologyIso f i).toLinearEquiv

def projection (n : ℕ) : (S).X₁ ⟶ BoundedProductCohomology.component (p := p) (J := J) (δ := δ) f n :=
  (S).f ≫ CountableProductHomology.projection R (BoundedProductCohomology.family (p := p) (J := J) (δ := δ) f) n

theorem lifted_projection (n : ℕ) : ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map (projection (p := p) (J := J) (δ := δ) f n) =
    BoundedResolutionLevels.projection f n := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem homology (n i : ℕ) (x : (S).X₁.homology i) :
    BoundedProductCohomology.componentLinearEquiv f n i (HomologicalComplex.homologyMap (projection f n) i x) =
      BoundedCrystalline.CrystallineCohomology.restriction f n i (sourceEquiv f i x) := by
  let e := BoundedResolution.Comparison.homologyIso (p := p) (J := J) (δ := δ) f i
  let d := BoundedResolutionLevels.homologyIso (p := p) (J := J) (δ := δ) f n i
  let g := ModuleCat.ofHom (BoundedCrystalline.CrystallineCohomology.restriction (p := p) (J := J) (δ := δ) f n i)
  have h : HomologicalComplex.homologyMap (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map (projection f n)) i ≫ d.hom = e.hom ≫ g :=
    (congrArg (fun b => HomologicalComplex.homologyMap b i ≫ d.hom) (lifted_projection f n)).trans
      (ResolutionProjectionExt.homology f n i)
  exact (congrArg (fun t => t (HomologicalComplex.homologyMap (projection f n) i x))
    (InverseTransitionCoordinates.componentEquiv f n i)).trans
      (Lifted.HomologyTransport.naturality.{u + 1, u + 1, u + 2} R (projection f n) i e d g h x)

theorem product_coordinate (n i : ℕ) (x : (S).X₁.homology i) :
    BoundedProductCohomology.productHomologyLinearEquiv f i (HomologicalComplex.homologyMap (S).f i x) n =
      BoundedCrystalline.CrystallineCohomology.restriction f n i (sourceEquiv f i x) := by
  have hp := congrArg (fun b => b (HomologicalComplex.homologyMap (S).f i x))
    (CountableProductHomology.homologyIso_projection R (BoundedProductCohomology.family (p := p) (J := J) (δ := δ) f) i n)
  have hm := congrArg (fun b => b x) (HomologicalComplex.homologyMap_comp (S).f
    (CountableProductHomology.projection R (BoundedProductCohomology.family (p := p) (J := J) (δ := δ) f) n) i)
  exact (congrArg (BoundedProductCohomology.componentLinearEquiv f n i) (hp.trans hm.symm)).trans (RestrictionJointKernel.homology f n i x)

theorem zero_of_restrictions (i : ℕ) [hF : Mono (HomologicalComplex.homologyMap (S).f i)]
    (x : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i)
    (hx : ∀ n, BoundedCrystalline.CrystallineCohomology.restriction f n i x = 0) : x = 0 := by
  let y := (sourceEquiv f i).symm x
  have hy : sourceEquiv f i y = x := (sourceEquiv f i).apply_symm_apply x
  have hy' : y = 0 := by
    apply @ProductHomologyKernel.zero_of_projections R inferInstance
      (BoundedProductCohomology.family (p := p) (J := J) (δ := δ) f) (S).X₁ (S).f i hF y
    intro n
    apply (BoundedProductCohomology.componentLinearEquiv f n i).injective
    exact (RestrictionJointKernel.homology f n i y).trans
      ((congrArg (BoundedCrystalline.CrystallineCohomology.restriction f n i) hy).trans
        ((hx n).trans (BoundedProductCohomology.componentLinearEquiv f n i).map_zero.symm))
  exact hy.symm.trans ((congrArg (sourceEquiv f i) hy').trans (sourceEquiv f i).map_zero)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RestrictionJointKernel
