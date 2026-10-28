import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrincipalCoefficients
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.RationalPointDivisor

/-! # Parent Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentSection.BundleCycles

noncomputable section

section

/-! A locally constructed supported principal cycle has the canonical class of the full finite pushforward whenever the actual fibers meeting the open are retained. The parent rational function is transported by the genuine open function-field isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {S N X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral S.left] [LocallyOfFiniteType S.hom] [AlgebraicGeometry.IsNoetherian S.left]
  [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left]
  (k : S ⟶ N) [IsFinite k.left] (a : X ⟶ S) [IsOpenImmersion a.left]

def finiteParentRationalFunction (r : X.left.functionField) : S.left.functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso a.left).inv r

omit [LocallyOfFiniteType S.hom] [AlgebraicGeometry.IsNoetherian S.left]
  [AlgebraicGeometry.IsNoetherian X.left] in
theorem finiteParentRationalFunction_pullback (r : X.left.functionField) :
    RationalDivisorRestriction.BundleCycles.openFunctionFieldMap a.left (finiteParentRationalFunction a r) = r :=
  Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso a.left) r

def finiteParentPrincipalCycle (n : ℕ) (r : X.left.functionField) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint N.hom n →₀ ℚ :=
  GradedOverPushforward.BundleCycles.finiteOverGradedPushforward k n
    (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n (finiteParentRationalFunction a r))

omit [IsFinite (Over.Hom.left k)] in
theorem finiteParentPrincipalCycle_coefficient (n : ℕ)
    (hn : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension S.hom = n + 1) (r : X.left.functionField)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint N.hom n)
    (hcover : ∀ y : S.left, k.left y = x.val → y ∈ Set.range a.left) :
    CycleClass.Thom.Point.Constructions.pointPushforward (a.left ≫ k.left)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X.left r) x.val =
    finiteParentPrincipalCycle k a n r x := by
  have he := CycleClass.Thom.Open.Principal.Constructions.FiberCoefficients.principalPointDivisor_open_fiber_coefficient
    a.left (finiteParentRationalFunction a r) k.left x.val hcover
  change CycleClass.Thom.Point.Constructions.pointPushforward (a.left ≫ k.left)
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X.left (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap a.left (finiteParentRationalFunction a r))) x.val = _ at he
  rw [finiteParentRationalFunction_pullback] at he
  have hf := GradedOverPushforward.BundleCycles.finiteOverGradedPushforward_forget k n
    (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n (finiteParentRationalFunction a r))
  rw [Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor_push S.left S.hom n hn] at hf
  have hc := congrArg (fun c : N.left →₀ ℚ => c x.val) hf
  rw [Open.CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply] at hc
  exact he.trans hc.symm

variable [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (T : Set U) (n q : ℕ)
  (hn : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension S.hom = n + 1)
  (hq : n + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

include hn in
omit [IsFinite (Over.Hom.left k)] in
theorem finiteSupportedPrincipalClass_eq_parent (r : X.left.functionField)
    (c : LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenSupportedCycle N U T n)
    (hc : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion N.hom n (LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenSupportedCycle_forget N U T n c) =
      CycleClass.Thom.Point.Constructions.pointPushforward (a.left ≫ k.left)
        (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X.left r))
    (hcover : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint N.hom n,
      (∃ x : U, x.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (irreducibleSetEquivPoints.symm D.val))) →
      ∀ y : S.left, k.left y = D.val → y ∈ Set.range a.left) :
    LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U T n q hq c =
    LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U T n q hq
      (LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle N U T n (finiteParentPrincipalCycle k a n r)) := by
  apply LineBundles.Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap_eq_restrict_of_local_coefficients N U T n q hq
  intro D hD
  have he := congrArg (fun c : N.left →₀ ℚ => c D.val) hc
  rw [Open.CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply] at he
  exact he.trans (finiteParentPrincipalCycle_coefficient k a n hn r D (hcover D hD))

end

section

/-! For sections pulled from the actual ambient scheme, the parent rational function constructed by the open field isomorphism is exactly the original section germ. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [IsIntegral X.left]
  (a : X ⟶ S) [IsOpenImmersion a.left]

local instance finiteParentSectionSourceTopNonempty : Nonempty (⊤ : X.left.Opens) :=
  ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩
local instance finiteParentSectionTargetTopNonempty : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

theorem finiteParentRationalFunction_globalSection (s : Γ(S.left, ⊤)) :
    finiteParentRationalFunction a (X.left.germToFunctionField ⊤ (a.left.appTop s)) =
    S.left.germToFunctionField ⊤ s := by
  apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso a.left).commRingCatIsoToRingEquiv.injective
  exact (finiteParentRationalFunction_pullback a _).trans
    (FiniteAffine.PrincipalCoefficients.BundleCycles.openFunctionFieldMap_globalSection a.left s).symm

variable {N Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (k : S ⟶ N) (g : X ⟶ Y) (j : Y ⟶ N)
  (hs : a ≫ k = g ≫ j)

include hs

omit [AlgebraicGeometry.IsIntegral S.left] [AlgebraicGeometry.IsIntegral X.left] [IsOpenImmersion (Over.Hom.left a)] in
theorem finiteSquare_globalSection (s : Γ(N.left, ⊤)) :
    g.left.appTop (j.left.appTop s) = a.left.appTop (k.left.appTop s) := by
  have he : a.left ≫ k.left = g.left ≫ j.left := congrArg Over.Hom.left hs
  have h := congrArg (fun m : X.left ⟶ N.left => m.appTop s) he
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h.symm

theorem finiteParentRationalFunction_baseSection (s : Γ(N.left, ⊤)) :
    finiteParentRationalFunction a (X.left.germToFunctionField ⊤ (g.left.appTop (j.left.appTop s))) =
    S.left.germToFunctionField ⊤ (k.left.appTop s) := by
  rw [finiteSquare_globalSection a k g j hs]
  exact finiteParentRationalFunction_globalSection a (k.left.appTop s)

end

/-! The parent cycle transported from a chart of an actual global section is exactly the finite pushforward of the original global section divisor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S N X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [LocallyOfFiniteType S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral X.left]
  (k : S ⟶ N) [IsFinite k.left] (a : X ⟶ S) [IsOpenImmersion a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) (hs : a ≫ k = g ≫ j)

local instance finiteParentGlobalSectionSourceTop : Nonempty (⊤ : X.left.Opens) :=
  ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩
local instance finiteParentGlobalSectionParentTop : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

include hs in
omit [LocallyOfFiniteType S.hom] [IsFinite (Over.Hom.left k)] in
theorem finiteParentPrincipalCycle_baseSection (n : ℕ) (s : Γ(N.left, ⊤)) :
    finiteParentPrincipalCycle k a n (X.left.germToFunctionField ⊤ (g.left.appTop (j.left.appTop s))) =
    GradedOverPushforward.BundleCycles.finiteOverGradedPushforward k n (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n
      (S.left.germToFunctionField ⊤ (k.left.appTop s))) :=
  congrArg (fun r => GradedOverPushforward.BundleCycles.finiteOverGradedPushforward k n (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor S.left S.hom n r))
    (finiteParentRationalFunction_baseSection a k g j hs s)

include hs in
omit [LocallyOfFiniteType S.hom] [AlgebraicGeometry.IsNoetherian S.left] [IsFinite (Over.Hom.left k)] in
theorem finiteChart_globalSection_germ_ne_zero (s : Γ(N.left, ⊤))
    (hsn : S.left.germToFunctionField ⊤ (k.left.appTop s) ≠ 0) :
    X.left.germToFunctionField ⊤ (g.left.appTop (j.left.appTop s)) ≠ 0 := by
  intro hz
  apply hsn
  have h := finiteParentRationalFunction_baseSection a k g j hs s
  rw [hz] at h
  exact h.symm.trans (map_zero (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso a.left).inv.hom)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentSection.BundleCycles
