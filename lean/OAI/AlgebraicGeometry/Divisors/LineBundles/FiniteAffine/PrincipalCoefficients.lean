import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.Principal

/-! # Principal Coefficients -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrincipalCoefficients.BundleCycles

noncomputable section

/-! Actual affine inverse-image charts retain entire finite fibers. Pulling a global section to these charts preserves every pushforward principal-divisor coefficient over the base open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X S : Scheme} [IsIntegral X] [IsIntegral S]
  (a : X ⟶ S) [IsOpenImmersion a]

local instance finiteAffinePrincipalSourceTopNonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, Opens.mem_top _⟩⟩
local instance finiteAffinePrincipalTargetTopNonempty : Nonempty (⊤ : S.Opens) :=
  ⟨⟨genericPoint S, Opens.mem_top _⟩⟩

theorem openFunctionFieldMap_globalSection (s : Γ(S, ⊤)) :
    RationalDivisorRestriction.BundleCycles.openFunctionFieldMap a (S.germToFunctionField ⊤ s) =
      X.germToFunctionField ⊤ (a.appTop s) := by
  have h := GenericFieldComposition.BundleCycles.genericFieldMap_germ_appLE a (genericPoint_eq_of_isOpenImmersion a)
    ⊤ ⊤ (by simp)
  have he : a.appLE ⊤ ⊤ (by simp) = a.appTop := by
    change a.app ⊤ ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) = a.app ⊤
    exact (congrArg (fun t => a.appTop ≫ t)
      (X.presheaf.map_id (Opposite.op (⊤ : X.Opens)))).trans (Category.comp_id _)
  rw [he] at h
  exact ConcreteCategory.congr_hom h s

variable {N : Over Foundations.Scheme.ProjectiveSpace.complexBase} {M : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  (k : M ⟶ N) [IsFinite k.left] (B : N.left.Opens)

omit [IsFinite k.left] in
theorem finiteAffineChart_algebraic_fiber_cover (x : N.left) (hx : x ∈ B) :
    ∀ y : M.left, k.left y = x → y ∈ Set.range (OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left := by
  intro y hy
  change y ∈ Set.range (k.left ⁻¹ᵁ B).ι
  rw [Scheme.Opens.range_ι]
  change k.left y ∈ B
  exact hy.symm ▸ hx

variable [IsIntegral M.left] [Nonempty (k.left ⁻¹ᵁ B)]
  [AlgebraicGeometry.IsNoetherian M.left]

local instance finiteAffinePrincipalSourceNoetherian :
    AlgebraicGeometry.IsNoetherian (OpenChart.BundleCycles.finiteAffineSource k B).left :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left

local instance finiteAffinePrincipalParentTopNonempty : Nonempty (⊤ : M.left.Opens) :=
  ⟨⟨genericPoint M.left, Opens.mem_top _⟩⟩
local instance finiteAffinePrincipalChartTopNonempty : Nonempty (⊤ : (OpenChart.BundleCycles.finiteAffineSource k B).left.Opens) :=
  ⟨⟨genericPoint (OpenChart.BundleCycles.finiteAffineSource k B).left, Opens.mem_top _⟩⟩

omit [IsFinite (Over.Hom.left k)] in
theorem finiteAffinePrincipal_coefficient (r : M.left.functionField) (x : N.left) (hx : x ∈ B) :
    CycleClass.Thom.Point.Constructions.pointPushforward
      ((OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left ≫ k.left)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (OpenChart.BundleCycles.finiteAffineSource k B).left
        (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left r)) x =
    CycleClass.Thom.Point.Constructions.pointPushforward k.left
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor M.left r) x :=
  CycleClass.Thom.Open.Principal.Constructions.FiberCoefficients.principalPointDivisor_open_fiber_coefficient
    (OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left r k.left x
    (finiteAffineChart_algebraic_fiber_cover k B x hx)

omit [IsFinite (Over.Hom.left k)] in
theorem finiteAffineSectionPrincipal_coefficient (s : Γ(M.left, ⊤)) (x : N.left) (hx : x ∈ B) :
    CycleClass.Thom.Point.Constructions.pointPushforward
      ((OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left ≫ k.left)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (OpenChart.BundleCycles.finiteAffineSource k B).left
        ((OpenChart.BundleCycles.finiteAffineSource k B).left.germToFunctionField ⊤
          ((OpenChart.BundleCycles.finiteAffineSourceInclusion k B).left.appTop s))) x =
    CycleClass.Thom.Point.Constructions.pointPushforward k.left
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor M.left (M.left.germToFunctionField ⊤ s)) x := by
  rw [← openFunctionFieldMap_globalSection]
  exact finiteAffinePrincipal_coefficient k B _ x hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrincipalCoefficients.BundleCycles
