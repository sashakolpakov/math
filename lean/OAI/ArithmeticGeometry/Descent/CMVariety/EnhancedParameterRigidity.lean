import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedParameterComplex
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyRigidity

/-! # Enhanced Parameter Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
An actual CM point supplies a smooth enhanced arithmetic parameter on
whose complex base change the literal fibers are locally isomorphic as
group schemes, preserving the full level and all original endomorphisms.
The parameter and CM tuple are constructed, not assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Topology

theorem EnhancedParameterRigidity.Abelian.presented_enhanced_tuple_recovery
    {g N r : ℕ} {δ : Fin g → ℕ} {A B : ModuliObjects.Abelian.EnhancedAbelianData g δ N r AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (e : ModuliObjects.Abelian.EnhancedAbelianIso A B) (P : StandardModuli.Abelian.ComplexAbelianPresentation B.polarized.abelian)
    (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety) (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin E.size) A.polarized.abelian)
    (h : AbelianEndomorphism.ConjugateAbelianTuples e.polarized.abelian a (E.onPresentedFiber P)) :
    ∀ i, (P.transportEnhanced e).comparison.inv ≫ a.map i ≫
      (P.transportEnhanced e).comparison.hom = E.map i :=
  fun i => PresentedTupleComparison.Abelian.conjugate_through_iso_recovery e.polarized.abelian P.comparison (E.map i) (a.map i) (h i)

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.native_local_retained_rigidity
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of ℚ)}
    {g N r : ℕ} {δ : Fin g → ℕ}
    {A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X} {p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X}
    (P : StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback p).polarized.abelian) (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety)
    (D : EnhancedChart.Abelian.SmoothEnhancedParameter f A p (E.onPresentedFiber P))
    (present : ∀ x : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X, StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback x).polarized.abelian)
    (hN : 0 < N) :
    ∀ᶠ s in 𝓝 D.nativeCenter,
      ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso D.nativeFamily.polarized.abelian
        D.nativeFamily.polarized.level D.nativeFamily.endomorphism D.nativeCenter s := by
  let G := D.nativeFamily.polarized.abelian
  let P₀ := D.nativeCenterPresentation P
  have hrec : ∀ i, P₀.comparison.inv ≫
      FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism D.nativeBase G (D.nativeExtraTuple.map i) D.nativeCenter ≫
        P₀.comparison.hom = E.map i :=
    EnhancedParameterRigidity.Abelian.presented_enhanced_tuple_recovery D.nativeCenterIso P E
      (D.nativeExtraTuple.pullback D.nativeCenter.left) D.native_extraRecovery
  let old : AbelianEndomorphism.AbelianEndomorphismTuple (Fin r) G :=
    ⟨D.nativeFamily.endomorphism, D.nativeFamily.endomorphism_group⟩
  exact FamilyRigidity.Abelian.FamilyPoints.smooth_family_preserves_retained_endomorphisms G (D.nativePresentation present)
    N hN D.nativeFamily.polarized.level D.nativeCenter P₀ E D.nativeExtraTuple hrec old

theorem EnhancedParameterRigidity.Abelian.cm_point_has_smooth_locally_rigid_enhanced_parameter
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    {g N r : ℕ} {δ : Fin g → ℕ} (A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X)
    (present : ∀ x : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X, StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback x).polarized.abelian)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback p).polarized.abelian)
    (hCM : P.variety.HasCMH1) (hN : 0 < N) :
    ∃ (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety) (D : EnhancedChart.Abelian.SmoothEnhancedParameter f A p (E.onPresentedFiber P)),
      ∀ᶠ s in 𝓝 D.nativeCenter,
        ConcreteFiberLevelRigidity.Abelian.FamilyPoints.ActualEquivariantLevelFiberIso D.nativeFamily.polarized.abelian
          D.nativeFamily.polarized.level D.nativeFamily.endomorphism D.nativeCenter s := by
  let E := AlgebraicEnhancement.Abelian.CMEnhancement.ofHasCM P.variety hCM
  obtain ⟨D⟩ := EnhancedChart.Abelian.smooth_enhanced_parameter_exists f A p (E.onPresentedFiber P)
  exact ⟨E, D, D.native_local_retained_rigidity P E present hN⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety
