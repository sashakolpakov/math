import OAI.AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport
import OAI.AlgebraicTopology.Duality.Poincare.CompactBallExhaustion
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportBallColimit
import OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Euclidean Compact Cohomology -/

namespace OAI.AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology

noncomputable section

/-!
# Compactly supported rational cohomology of complex coordinate space

The top-degree normalization is evaluation on the actual compact-support
orientation class. Closed coordinate balls give the cofinal supports on which
the relative groups can be computed explicitly, including complex dimension zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The compact coordinate orientation classes are compatible with the actual
relative homology restrictions for every inclusion of compact supports. -/
theorem complexCompactSupportClass_restriction (d : ℕ)
    (K L : Set (Fin d → ℂ)) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of (Fin d → ℂ)) hKL) (2 * d)
        (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d L hL) =
      AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d K hK := by
  apply AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles.euclidean_compactSupport_point_ext d K hK
  intro x hx
  exact (ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.relativeComplementHomologyRestriction_toPoint
      (TopCat.of (Fin d → ℂ)) hKL x hx (2 * d))
    (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d L hL)).trans
      ((AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint d L hL x (hKL hx)).trans
        (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint d K hK x hx).symm)

/-- On a coordinate closed ball, the compact orientation is the already
constructed closed-ball relative class, not an independently chosen generator. -/
theorem complexCompactSupportClass_closedBall (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d (Metric.closedBall (0 : Fin d → ℂ) r)
        (isCompact_closedBall _ _) = AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallClass d r hr := by
  apply AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles.euclidean_compactSupport_point_ext d _ (isCompact_closedBall _ _)
  intro x hx
  rw [AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint, AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.localHomologyToPoint_closedBall,
    AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallClass_atPoint]

/-- The rational dual of a specified integral rank-one module is normalized
by evaluating at the inverse image of one. -/
def integralRankOneRationalDualEquiv (M : ModuleCat.{0} ℤ) (e : M ≃ₗ[ℤ] ℤ) :
    (M →ₗ[ℤ] ℚ) ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.congrLeft ℚ ℚ e).trans (LinearMap.ringLmapEquivSelf ℤ ℚ ℚ)

@[simp]
theorem integralRankOneRationalDualEquiv_apply (M : ModuleCat.{0} ℤ)
    (e : M ≃ₗ[ℤ] ℤ) (f : M →ₗ[ℤ] ℚ) :
    integralRankOneRationalDualEquiv M e f = f (e.symm 1) := rfl

/-- The dual of actual closed-ball top homology, normalized by its actual class. -/
def complexClosedBallRationalDualEquiv (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) (2 * d) →ₗ[ℤ] ℚ) ≃ₗ[ℚ] ℚ :=
  integralRankOneRationalDualEquiv _ (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallTopHomologyIso d r hr).toLinearEquiv

@[simp]
theorem complexClosedBallRationalDualEquiv_apply (d : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (f : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) (2 * d) →ₗ[ℤ] ℚ) :
    complexClosedBallRationalDualEquiv d r hr f = f (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallClass d r hr) := rfl

/-- Rational duals of the remaining actual closed-ball homology groups vanish. -/
theorem complexClosedBallRationalDual_isZero (d n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hn : n ≠ 2 * d) :
    IsZero (ModuleCat.of ℚ (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) n →ₗ[ℤ] ℚ)) := by
  let : Subsingleton (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) n) :=
    ModuleCat.isZero_iff_subsingleton.mp (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallHomology_isZero d n r hr hn)
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual relative rational cohomology of a closed coordinate ball in
top degree, with normalization inherited from evaluation on its integral class. -/
def complexClosedBallTopCohomologyEquiv (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) (2 * d) ≃ₗ[ℚ] ℚ :=
  (RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of (Fin d → ℂ))
    (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) (2 * d)).trans
      (complexClosedBallRationalDualEquiv d r hr)

@[simp]
theorem complexClosedBallTopCohomologyEquiv_apply (d : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) (2 * d)) :
    complexClosedBallTopCohomologyEquiv d r hr c =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
        (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) (2 * d) c
        (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallClass d r hr) := rfl

/-- The remaining rational relative cohomology degrees of a closed ball vanish. -/
theorem complexClosedBallCohomology_isZero (d n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hn : n ≠ 2 * d) :
    IsZero (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) n) :=
  RelativeUniversalCoefficient.relativeRationalCohomology_isZero_of_homology_isZero (TopCat.of (Fin d → ℂ))
    (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) r) n (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexClosedBallHomology_isZero d n r hr hn)

/-- Top-degree evaluation on the actual orientation class with a specified
compact support. The support need not be convex, nonempty, or connected. -/
def complexCompactSupportEvaluation (d : ℕ) (K : Compacts (Fin d → ℂ)) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d) ⟶ ModuleCat.of ℚ ℚ :=
  ModuleCat.ofHom ((LinearMap.applyₗ' ℚ (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d K K.isCompact)).comp
    (RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d)))

@[simp]
theorem complexCompactSupportEvaluation_apply (d : ℕ) (K : Compacts (Fin d → ℂ))
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d)) :
    complexCompactSupportEvaluation d K c =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
        (K : Set (Fin d → ℂ))ᶜ (2 * d) c
        (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d K K.isCompact) := rfl

/-- Compact-support enlargement preserves the pairing with the compatible
actual compact orientation classes. -/
@[reassoc]
theorem complexCompactSupportEvaluation_naturality (d : ℕ)
    {K L : Compacts (Fin d → ℂ)} (hKL : K ≤ L) :
    CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hKL (2 * d) ≫
        complexCompactSupportEvaluation d L = complexCompactSupportEvaluation d K := by
  ext c
  let hmap : Set.MapsTo (𝟙 (TopCat.of (Fin d → ℂ)))
      (L : Set (Fin d → ℂ))ᶜ (K : Set (Fin d → ℂ))ᶜ := fun _ hx hxK => hx (hKL hxK)
  change RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
      (L : Set (Fin d → ℂ))ᶜ (2 * d)
      (HomologicalComplex.homologyMap
        (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
          (𝟙 (TopCat.of (Fin d → ℂ))) hmap) (2 * d) c)
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d L L.isCompact) = _
  rw [RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality]
  change RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d) c
      (HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction (TopCat.of (Fin d → ℂ)) hKL) (2 * d)
        (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d L L.isCompact)) = _
  rw [complexCompactSupportClass_restriction]
  rfl

/-- The normalized top-degree map on the actual compact-support cohomology
colimit, obtained from evaluation at every compact support. -/
def complexCompactSupportedEvaluation (d : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d) ⟶
      ModuleCat.of ℚ ℚ :=
  CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d)
    (complexCompactSupportEvaluation d)
    (fun _ _ h => complexCompactSupportEvaluation_naturality d h)

@[reassoc (attr := simp)]
theorem complexCompactSupportedEvaluation_ι (d : ℕ) (K : Compacts (Fin d → ℂ)) :
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) K (2 * d) ≫
        complexCompactSupportedEvaluation d = complexCompactSupportEvaluation d K :=
  CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d)
    (complexCompactSupportEvaluation d)
    (fun _ _ h => complexCompactSupportEvaluation_naturality d h) K

@[simp]
theorem complexCompactSupportedEvaluation_ι_apply (d : ℕ) (K : Compacts (Fin d → ℂ))
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d)) :
    complexCompactSupportedEvaluation d
      (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) K (2 * d) c) =
      complexCompactSupportEvaluation d K c :=
  ConcreteCategory.congr_hom (complexCompactSupportedEvaluation_ι d K) c

/-- The top cohomology equivalence for the explicitly indexed cofinal balls. -/
def complexBallSupportTopCohomologyEquiv (d i : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (CompactBallExhaustion.compactBallSupport (Fin d → ℂ) i : Set (Fin d → ℂ))ᶜ (2 * d) ≃ₗ[ℚ] ℚ :=
  complexClosedBallTopCohomologyEquiv d ((i : ℝ) + 1) (by positivity)

/-- Evaluation at a cofinal ball agrees with its already normalized isomorphism. -/
theorem complexCompactSupportEvaluation_ball (d i : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (CompactBallExhaustion.compactBallSupport (Fin d → ℂ) i : Set (Fin d → ℂ))ᶜ (2 * d)) :
    complexCompactSupportEvaluation d (CompactBallExhaustion.compactBallSupport (Fin d → ℂ) i) c =
      complexBallSupportTopCohomologyEquiv d i c := by
  rw [complexCompactSupportEvaluation_apply]
  change RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles.OutsideClosedBall (Fin d → ℂ) ((i : ℝ) + 1)) (2 * d) c
      (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d (Metric.closedBall 0 ((i : ℝ) + 1))
        (isCompact_closedBall _ _)) = _
  rw [complexCompactSupportClass_closedBall d _ (by positivity)]
  rfl

/-- Injectivity follows by representing each class on a cofinal ball, where
the normalized evaluation map is already an isomorphism. -/
theorem complexCompactSupportedEvaluation_injective (d : ℕ) :
    Function.Injective (complexCompactSupportedEvaluation d) := by
  apply (injective_iff_map_eq_zero (complexCompactSupportedEvaluation d).hom).mpr
  intro c hc
  obtain ⟨i, a, rfl⟩ := CompactSupportBallColimit.compactSupportedCohomology_exists_ball_stage
    (ModuleCat.of ℚ ℚ) (Fin d → ℂ) (2 * d) c
  rw [complexCompactSupportedEvaluation_ι_apply, complexCompactSupportEvaluation_ball] at hc
  have ha : a = 0 := (complexBallSupportTopCohomologyEquiv d i).injective
    (hc.trans (map_zero (complexBallSupportTopCohomologyEquiv d i)).symm)
  rw [ha, map_zero]

/-- Every rational number is realized already on the first cofinal ball. -/
theorem complexCompactSupportedEvaluation_surjective (d : ℕ) :
    Function.Surjective (complexCompactSupportedEvaluation d) := by
  intro q
  refine ⟨CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
    (CompactBallExhaustion.compactBallSupport (Fin d → ℂ) 0) (2 * d)
    ((complexBallSupportTopCohomologyEquiv d 0).symm q), ?_⟩
  rw [complexCompactSupportedEvaluation_ι_apply, complexCompactSupportEvaluation_ball,
    LinearEquiv.apply_symm_apply]

/-- Actual compactly supported rational cohomology of complex coordinate
space in its real top degree. This includes `d = 0`. -/
def complexCompactSupportedTopCohomologyEquiv (d : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d) ≃ₗ[ℚ] ℚ :=
  LinearEquiv.ofBijective (complexCompactSupportedEvaluation d).hom
    ⟨complexCompactSupportedEvaluation_injective d,
      complexCompactSupportedEvaluation_surjective d⟩

@[simp]
theorem complexCompactSupportedTopCohomologyEquiv_apply (d : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d)) :
    complexCompactSupportedTopCohomologyEquiv d c = complexCompactSupportedEvaluation d c := rfl

/-- The global top-degree normalization is actual evaluation on the compact
orientation class at every support, not merely an abstract dimension statement. -/
theorem complexCompactSupportedTopCohomologyEquiv_stage (d : ℕ)
    (K : Compacts (Fin d → ℂ))
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d)) :
    complexCompactSupportedTopCohomologyEquiv d
      (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) K (2 * d) c) =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
        (K : Set (Fin d → ℂ))ᶜ (2 * d) c
        (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d K K.isCompact) := by
  rw [complexCompactSupportedTopCohomologyEquiv_apply,
    complexCompactSupportedEvaluation_ι_apply, complexCompactSupportEvaluation_apply]

/-- All compactly supported rational cohomology degrees other than the real
top degree vanish, since every class is represented on a cofinal closed ball. -/
theorem complexCompactSupportedCohomology_isZero (d n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) n) := by
  have hz (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Fin d → ℂ)) n) : c = 0 := by
    obtain ⟨i, a, rfl⟩ := CompactSupportBallColimit.compactSupportedCohomology_exists_ball_stage
      (ModuleCat.of ℚ ℚ) (Fin d → ℂ) n c
    let : Subsingleton (Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Fin d → ℂ))
        (CompactBallExhaustion.compactBallSupport (Fin d → ℂ) i : Set (Fin d → ℂ))ᶜ n) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (complexClosedBallCohomology_isZero d n ((i : ℝ) + 1) (by positivity) hn)
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero]
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- The complementary-degree version uses the honest equation `p + q = 2*d`;
no truncated natural subtraction is used. -/
theorem complexCompactSupportedCohomology_positiveComplement_isZero
    (d p q : ℕ) (hpq : p + q = 2 * d) (hq : q ≠ 0) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) p) :=
  complexCompactSupportedCohomology_isZero d p (by omega)

end

end OAI.AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology
