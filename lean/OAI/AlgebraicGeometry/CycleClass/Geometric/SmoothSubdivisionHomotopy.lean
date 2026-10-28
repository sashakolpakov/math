import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothNaturalHomotopy
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision

/-! # Smooth Subdivision Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# A subdivision homotopy inside actual smooth singular chains

The signed geometric subdivision preserves every singular structure closed
under smooth simplex substitution. Its naturality follows by the injective
inclusion into ordinary singular chains. The genuine smooth model fillings
then give a natural homotopy to the identity, without asserting smoothness of
any pre-existing continuous filler.
-/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual inclusion from specified smooth chains into ordinary chains. -/
abbrev SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) : SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X ⟶ LocalHomology.Cycles.integralSingularChains X.space :=
  AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision.subcomplexIntegralChainInclusion X.space X.smooth

/-- The inclusion is injective on the actual chain modules. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_injective (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) (n : ℕ) :
    Function.Injective ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n) :=
  AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision.subcomplexIntegralChainInclusion_injective X.space X.smooth n

/-- The smooth-to-continuous inclusion is natural for all the concrete morphisms. -/
@[reassoc]
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_naturality {X Y : SmoothSimplexModels.Cycles.SmoothSimplexSpace} (f : X ⟶ Y) :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f ≫ SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion Y = SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X ≫ LocalHomology.Cycles.integralSingularChainFunctor.map f.map := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (SmoothSimplexModels.Cycles.SmoothSimplexSpace.mapSmooth f) ≫
      ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map Y.smooth.ι = _
  rw [← Functor.map_comp, SmoothSimplexModels.Cycles.SmoothSimplexSpace.mapSmooth_inclusion, Functor.map_comp]
  rfl

/-- Pointwise naturality, in the concrete chain modules. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_chainMap_apply {X Y : SmoothSimplexModels.Cycles.SmoothSimplexSpace} (f : X ⟶ Y) (n : ℕ)
    (c : (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X).X n) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion Y).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n c) =
      (LocalHomology.Cycles.integralSingularChainFunctor.map f.map).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n c) :=
  ConcreteCategory.congr_hom (congrArg (fun g => g.f n) (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_naturality f)) c

/-- Every actual barycentric cell has the required smooth substitution property. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_closed (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) {n : ℕ}
    (s : X.smooth.toSSet.obj (.op ⦋n⦌)) (σ : Equiv.Perm (Fin (n + 1))) :
    SubdivisionOperator.Cycles.subdivisionSimplex X.space n s.val σ ∈ X.smooth.obj (.op ⦋n⦌) := by
  have hs : (X.space.toSSetObjEquiv (.op ⦋n⦌)).symm
      (X.space.toSSetObjEquiv (.op ⦋n⦌) s.val) ∈ X.smooth.obj (.op ⦋n⦌) := by
    simpa only [Equiv.symm_apply_apply] using s.property
  exact X.precomp_mem (X.space.toSSetObjEquiv (.op ⦋n⦌) s.val) hs
    (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.isSmoothSimplexIn_barycentricSubdivisionMap σ)

/-- Signed geometric subdivision on the actual smooth chain complex. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) : SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X :=
  AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision.subcomplexSubdivisionChainMap X.space X.smooth (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_closed X)

/-- Inclusion carries the smooth subdivision to the ordinary geometric subdivision. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_subdivision_apply (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) (n : ℕ)
    (c : (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X).X n) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X).f n c) =
      SubdivisionOperator.Cycles.subdivisionDegree X.space n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n c) :=
  AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision.subcomplexSubdivisionDegree_inclusion X.space X.smooth (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_closed X) n c

/-- Actual smooth subdivision is natural under every continuous map preserving
the specified smooth singular structures. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_naturality {X Y : SmoothSimplexModels.Cycles.SmoothSimplexSpace} (f : X ⟶ Y) (n : ℕ) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision Y).f n =
      (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X).f n ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_injective Y n
  change (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion Y).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision Y).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n c)) =
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion Y).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X).f n c))
  rw [SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_subdivision_apply, SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_chainMap_apply,
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_chainMap_apply, SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion_subdivision_apply]
  exact (SubdivisionNaturality.Cycles.subdivisionDegree_naturality_apply f.map n ((SmoothSimplexModels.Cycles.SmoothSimplexSpace.inclusion X).f n c)).symm

/-- Geometric subdivision as a natural endomorphism of actual smooth chains. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivision : SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains ⟶ SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains where
  f n :=
    { app X := (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X).f n
      naturality _ _ f := SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_naturality f n }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    exact (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X).comm i j

theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivision_zero :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivision.f 0 = 𝟙 (SmoothSimplexModels.Cycles.SmoothSimplexSpace.degreeFunctor 0) := by
  apply NatTrans.ext
  funext X
  exact AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision.subcomplexSubdivisionChainMap_f_zero X.space X.smooth (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_closed X)

/-- The smooth model construction gives a natural smooth subdivision homotopy. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivisionHomotopy : Homotopy SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivision (𝟙 SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains) :=
  SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalHomotopy SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivision (𝟙 SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalChains) SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivision_zero

/-- Actual smooth subdivision is homotopic to identity inside smooth chains. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy (X : SmoothSimplexModels.Cycles.SmoothSimplexSpace) :
    Homotopy (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision X) (𝟙 (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chains X)) :=
  SmoothSimplexModels.Cycles.SmoothSimplexSpace.homotopyAt SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivisionHomotopy X

/-- The homotopy itself is natural for maps preserving the actual smooth structures. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy_naturality {X Y : SmoothSimplexModels.Cycles.SmoothSimplexSpace} (f : X ⟶ Y)
    (i j : ℕ) :
    (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f i ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy Y).hom i j =
      (SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy X).hom i j ≫ (SmoothSimplexModels.Cycles.SmoothSimplexSpace.chainMap f).f j :=
  (SmoothSimplexModels.Cycles.SmoothSimplexSpace.naturalSubdivisionHomotopy.hom i j).naturality f

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- The general geometric operator is exactly the previously defined manifold operator. -/
theorem SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision_ofManifold :
    SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivision (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M) = AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M := rfl

/-- The resulting homotopy has precisely the actual manifold-smooth endpoints. -/
def SmoothSimplexModels.Cycles.SmoothSimplexSpace.manifoldSmoothSubdivisionHomotopy :
    Homotopy (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothSubdivisionChainMap E M)
      (𝟙 (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSubdivision.manifoldSmoothIntegralChains E M)) :=
  SmoothSimplexModels.Cycles.SmoothSimplexSpace.subdivisionHomotopy (SmoothSimplexModels.Cycles.SmoothSimplexSpace.ofManifold E M)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
