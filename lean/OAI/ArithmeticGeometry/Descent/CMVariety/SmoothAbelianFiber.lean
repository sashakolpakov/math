import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianTupleSpread
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedTupleComparison
import OAI.ArithmeticGeometry.Descent.CMVariety.PulledBackPresentations

/-! # Smooth Abelian Fiber -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianFiber

noncomputable section

/-! Smooth arithmetic parameters retaining an actual abelian fiber and
an exact prescribed finite tuple of group endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def pullbackComplexFiberPresentations {g : ℕ} {S T : Scheme}
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : T ⟶ S)
    (present : ∀ p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback p)) :
    ∀ p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T, StandardModuli.Abelian.ComplexAbelianPresentation ((G.pullback f).pullback p) :=
  fun p => StandardModuli.Abelian.ComplexAbelianPresentation.pullbackComp G f p (present (p ≫ f))

structure SmoothAbelianParameter {g : ℕ} {Index : Type}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (k : AbelianEndomorphism.AbelianEndomorphismTuple Index A) where
  space : Scheme
  rationalStructure : space ⟶ Spec (CommRingCat.of ℚ)
  smooth : Smooth rationalStructure
  family : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g space
  point : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ space
  fiberComparison : (family.pullback point).scheme ≅ A.scheme
  fiberComparison_group : IsMonHom fiberComparison.hom
  extraTuple : AbelianEndomorphism.AbelianEndomorphismTuple Index family
  extraRecovery : AbelianEndomorphism.ConjugateAbelianTuples fiberComparison (extraTuple.pullback point) k
  present : ∀ p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ space, StandardModuli.Abelian.ComplexAbelianPresentation (family.pullback p)

attribute [instance] SmoothAbelianParameter.smooth SmoothAbelianParameter.fiberComparison_group

theorem smooth_abelian_parameter_exists
    (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [Algebra.Smooth ℚ R]
    [Algebra R ℂ] (hR : Function.Injective (algebraMap R ℂ))
    {Index : Type} [Fintype Index] {g : ℕ}
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R)))
    (present : ∀ p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (CommRingCat.of R), StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback p))
    (k : AbelianEndomorphism.AbelianEndomorphismTuple Index (G.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))) :
    Nonempty (SmoothAbelianParameter
      (G.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) k) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℚ R
  have : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  have hbase : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℚ R))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  obtain ⟨s, t, U, _, hs, q, hq, a, ha⟩ :=
    SmoothAbelianTupleSpread.abelian_endomorphism_tuple_spreads_over_smooth_neighborhood R hR G k
  let f₁ := FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R ℂ s.unop
  let f₂ := FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t.unop
  let B := AbelianEndomorphism.twoStageCoefficientFamily R ℂ G s t
  let p := AbelianCoefficientComparison.coefficientInclusion (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop) ℂ t
  let e := RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison B U.ι q p hq
    (G.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (AbelianEndomorphism.twoStageCoefficientComparison R ℂ G s t)
  have : Smooth (U.ι ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t) := hs
  refine ⟨{
    space := U
    rationalStructure := (U.ι ≫ AbelianEndomorphism.twoStageCoefficientBaseMap R ℂ s t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
    smooth := inferInstance
    family := B.pullback U.ι
    point := q
    fiberComparison := e
    fiberComparison_group := inferInstance
    extraTuple := a
    extraRecovery := ha
    present := pullbackComplexFiberPresentations B U.ι
      (pullbackComplexFiberPresentations (G.pullback f₁) f₂
        (pullbackComplexFiberPresentations G f₁ present)) }⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianFiber
