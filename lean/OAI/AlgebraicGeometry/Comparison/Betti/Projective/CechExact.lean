import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafForgetAdditive
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing

/-! # Cech Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechExact.Dolbeault

noncomputable section

section

/-! Both actual projective comparison functors are additive and therefore preserve finite sums. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

instance projectiveAnalytifiedAdditiveFunctor_additive (n : ℕ) :
    (ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).Additive := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let F := Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X
  let G := SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)
  let : F.Additive := Analytification.ModuleExact.holomorphicModuleAnalytification_additive X
  let : G.Additive := Module.SheafForgetAdditive.Local.moduleSheafForget_additive (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)
  constructor
  intro M N f g
  exact (congrArg G.map (F.map_add (f := f) (g := g))).trans
    (G.map_add (f := F.map f) (g := F.map g))

instance projectiveAlgebraicModuleCechFunctor_additive (n : ℕ) :
    (ModuleFunctor.Dolbeault.projectiveAlgebraicModuleCechFunctor n).Additive := by
  let F := SheafOfModules.toSheaf.{0} (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
  let G := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)
  let : F.Additive := Module.SheafForgetAdditive.Local.moduleSheafForget_additive
    (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
  let : G.Additive := Cech.FunctorAdditive.nativeSheafCechFunctor_additive
    (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)
  constructor
  intro M N f g
  exact (congrArg G.map (F.map_add (f := f) (g := g))).trans
    (G.map_add (f := F.map f) (g := F.map g))

instance projectiveAnalyticModuleCechFunctor_additive (n : ℕ) :
    (ModuleFunctor.Dolbeault.projectiveAnalyticModuleCechFunctor n).Additive := by
  let F := ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n
  let G := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor
    (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Intersections.Dolbeault.projectiveStandardCover n)
  let : F.Additive := projectiveAnalytifiedAdditiveFunctor_additive n
  let : G.Additive := Cech.FunctorAdditive.nativeSheafCechFunctor_additive
    (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Intersections.Dolbeault.projectiveStandardCover n)
  constructor
  intro M N f g
  exact (congrArg G.map (F.map_add (f := f) (g := g))).trans
    (G.map_add (f := F.map f) (g := F.map g))

end

section

/-! Acyclic intersections give actual short exact sequences on both sides of the projective comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAlgebraicCechAcyclic (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) : Prop :=
  SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)
    ((SheafOfModules.toSheaf.{0} (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf).obj M)

theorem projectiveAlgebraicModuleCechFunctor_shortExact (n : ℕ)
    (S : ShortComplex (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) (hS : S.ShortExact)
    (h₁ : projectiveAlgebraicCechAcyclic n S.X₁) :
    (S.map (ModuleFunctor.Dolbeault.projectiveAlgebraicModuleCechFunctor n)).ShortExact := by
  let G := SheafOfModules.toSheaf.{0} (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
  let : G.Additive := Module.SheafForgetAdditive.Local.moduleSheafForget_additive
    (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
  let : PreservesFiniteColimits G := Module.SheafForgetAdditive.Local.moduleSheafForget_preservesFiniteColimits
    (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf
  let hGzero : G.PreservesZeroMorphisms := { map_zero := fun _ _ => G.mapAddHom.map_zero }
  have hGlim : PreservesFiniteLimits G := inferInstance
  have hGcolim : PreservesFiniteColimits G := inferInstance
  let T := @ShortComplex.map _ _ _ _ _ _ S G hGzero
  have hT : T.ShortExact :=
    @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ S hS G hGzero hGlim hGcolim
  exact Cech.FunctorAdditive.cechSheafComplexFunctor_shortExact (X := TopCat.of (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) T hT h₁

theorem projectiveAnalyticModuleCechFunctor_shortExact (n : ℕ)
    (S : ShortComplex (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) (hS : S.ShortExact)
    (h₁ : ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n S.X₁) :
    (S.map (ModuleFunctor.Dolbeault.projectiveAnalyticModuleCechFunctor n)).ShortExact := by
  let G := ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n
  let : G.Additive := projectiveAnalytifiedAdditiveFunctor_additive n
  let hGzero : G.PreservesZeroMorphisms := { map_zero := fun _ _ => G.mapAddHom.map_zero }
  have hGlim : PreservesFiniteLimits G := ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor_preservesFiniteLimits n
  have hGcolim : PreservesFiniteColimits G := ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor_preservesFiniteColimits n
  let T := @ShortComplex.map _ _ _ _ _ _ S G hGzero
  have hT : T.ShortExact :=
    @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ S hS G hGzero hGlim hGcolim
  exact Cech.FunctorAdditive.cechSheafComplexFunctor_shortExact (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
    (Intersections.Dolbeault.projectiveStandardCover n) T hT h₁

end

/-! Quasicoherent projective modules have acyclic algebraic coordinate intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem projectiveAlgebraicCechAcyclic_quasicoherent (n : ℕ)
    (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) [M.IsQuasicoherent] :
    projectiveAlgebraicCechAcyclic n M := by
  have : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).IsSeparated := by
    constructor
    rw [← terminal.comp_from (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)]
    infer_instance
  intro p t q
  let V : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens := ∏ᶜ fun k : Fin (p + 1) => Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n (t k)
  have : IsAffine V.toScheme :=
    SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n) p t
  change Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.restrictFunctor V.ι).obj M) (q + 1))
  exact SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton _ q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechExact.Dolbeault
