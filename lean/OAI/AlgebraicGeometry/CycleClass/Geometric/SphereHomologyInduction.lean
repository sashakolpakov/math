import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso
import Mathlib.Analysis.Normed.Module.Connected

/-! # Sphere Homology Induction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles

noncomputable section

/-!
# Integral singular homology of Euclidean unit spheres

The sphere models are actual metric unit spheres, and their homology is
the homology of mathlib's integral singular chain complex. The low-degree
calculations use the actual two-point model, path connectedness, and the
small-chain Mayer–Vietoris sequence. The proved open-cover comparison
then transfers those calculations and the higher-degree shift to ordinary
singular homology. The dimension induction yields the integer top group
and vanishing of all other positive-degree groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The standard `d`-sphere, as the metric unit sphere in real Euclidean
space of dimension `d+1`, with its subspace topology. -/
abbrev standardSphere (d : ℕ) : TopCat.{0} :=
  TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (d + 1))))

/-- The actual integral singular homology of the specified unit sphere. -/
abbrev standardSphereHomology (d n : ℕ) : ModuleCat.{0} ℤ :=
  RelativeHomologyExact.Cycles.integralSingularHomology (standardSphere d) n

/-- The unit sphere in a Euclidean line is the explicit two-point model. -/
def standardZeroSphereHomeomorph : standardSphere 0 ≃ₜ ZeroSphere.Cycles.zeroSphere :=
  SmallCircleHomology.Cycles.euclideanLineSphereHomeomorph.trans ZeroSphere.Cycles.zeroSphereRealHomeomorph.symm

/-- The actual homology comparison with the explicit two-point sphere. -/
def standardZeroSphereHomologyIso (n : ℕ) :
    standardSphereHomology 0 n ≅ RelativeHomologyExact.Cycles.integralSingularHomology ZeroSphere.Cycles.zeroSphere n :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
    (X := standardSphere 0) (Y := ZeroSphere.Cycles.zeroSphere)
    standardZeroSphereHomeomorph.toHomotopyEquiv n

/-- The exceptional degree-zero answer for the zero-dimensional sphere. -/
def standardZeroSphereH0Iso :
    standardSphereHomology 0 0 ≅ ModuleCat.of ℤ (Fin 2 → ℤ) :=
  standardZeroSphereHomologyIso 0 ≪≫ ZeroSphere.Cycles.zeroSphereH0Iso

/-- Every positive-degree homology group of the zero-sphere is zero. -/
theorem standardZeroSphere_higherHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (standardSphereHomology 0 n) :=
  (ZeroSphere.Cycles.zeroSphere_higherHomology_isZero n hn).of_iso (standardZeroSphereHomologyIso n)

/-- Every positive-dimensional standard sphere is path connected. -/
instance standardSphere_pathConnectedSpace (d : ℕ) :
    PathConnectedSpace (standardSphere (d + 1)) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · apply Module.one_lt_rank_of_one_lt_finrank
    simp only [finrank_euclideanSpace_fin]
    omega
  · norm_num

/-- For a positive-dimensional sphere, augmentation gives its actual
degree-zero integral homology isomorphism. -/
def standardSphereH0Iso (d : ℕ) :
    standardSphereHomology (d + 1) 0 ≅ ModuleCat.of ℤ ℤ :=
  ContractibleModel.Cycles.integralSingularH0Iso (standardSphere (d + 1))

/-- Above the circle dimension, the two opposite-pole charts have a path
connected overlap: stereographic coordinates identify it with a punctured
real vector space of dimension at least two. -/
theorem standardSphereOverlap_pathConnectedSpace (d : ℕ) :
    PathConnectedSpace ↥(SphereCover.Cycles.spherePoleOpen (SphereCover.Cycles.standardSphereNorthPole (d + 2)) ∩
      SphereCover.Cycles.spherePoleOpen (-SphereCover.Cycles.standardSphereNorthPole (d + 2))) := by
  let v := SphereCover.Cycles.standardSphereNorthPole (d + 2)
  have hdim := SphereCover.Cycles.sphereEquatorSpace_finrank v
  simp only [finrank_euclideanSpace_fin] at hdim
  have hdim' : 1 < Module.finrank ℝ (SphereCover.Cycles.SphereEquatorSpace v) := by omega
  let : PathConnectedSpace (NormalSphere.Cycles.PuncturedNormal (SphereCover.Cycles.SphereEquatorSpace v)) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank
        (Module.one_lt_rank_of_one_lt_finrank hdim') 0)
  exact (SphereCover.Cycles.spherePoleIntersectionChart v).symm.surjective.pathConnectedSpace
    (SphereCover.Cycles.spherePoleIntersectionChart v).symm.continuous

/-- Two contractible pieces with path connected intersection have zero
first homology in their actual small-chain complex. -/
theorem smallMayerVietoris_H1_isZero_of_pathConnected_intersection
    (X : TopCat.{0}) (U V : Set X) [ContractibleSpace U] [ContractibleSpace V]
    [PathConnectedSpace ↥(U ∩ V)] :
    IsZero (SmallMayerVietoris.Cycles.binarySmallSingularHomology X U V 1) := by
  have haug : RelativeHomologyExact.Cycles.integralSingularHomologyMap
      (SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)) 0 ≫
      (ContractibleModel.Cycles.integralSingularH0Iso (TopCat.of U)).hom =
      (ContractibleModel.Cycles.integralSingularH0Iso (TopCat.of ↥(U ∩ V))).hom :=
    HomologyZeroNaturality.Cycles.integralSingularH0_augmentation_naturality _
  have hinc : Mono (RelativeHomologyExact.Cycles.integralSingularHomologyMap
      (SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : U ∩ V ⊆ U)) 0) :=
    mono_of_mono_fac haug
  have hfirst : Mono (HomologicalComplex.homologyMap (SmallMayerVietoris.Cycles.smallMayerVietorisSequence X U V).f 0) :=
    @mono_of_mono_fac _ _ _ _ _ _ _ _ hinc
      (SmallMayerVietoris.Cycles.smallMayerVietoris_homology_f_fst X U V 0)
  have hboundary : Mono (SmallMayerVietoris.Cycles.smallMayerVietorisBoundary X U V 0) :=
    (SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X U V).mono_δ 1 0 rfl
      (SmallSphereHomology.Cycles.smallMayerVietorisMiddleHomology_isZero X U V 1
        (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ 1 (by decide))
        (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ 1 (by decide)))
  apply @IsZero.of_mono_eq_zero _ _ _ _ _
    (SmallMayerVietoris.Cycles.smallMayerVietorisBoundary X U V 0) hboundary
  let := hfirst
  apply (cancel_mono (HomologicalComplex.homologyMap (SmallMayerVietoris.Cycles.smallMayerVietorisSequence X U V).f 0)).mp
  exact ((SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X U V).δ_comp 1 0 rfl).trans
    (zero_comp).symm

/-- The higher-dimensional sphere's actual two-chart small complex has
zero first homology; all connectedness hypotheses are discharged. -/
theorem standardSphereSmallH1_isZero (d : ℕ) :
    IsZero (SmallSphereHomology.Cycles.spherePoleSmallHomology (SphereCover.Cycles.standardSphereNorthPole (d + 2)) 1) := by
  let := SphereCover.Cycles.spherePoleOpen_contractible (SphereCover.Cycles.standardSphereNorthPole (d + 2))
  let := SphereCover.Cycles.spherePoleOpen_contractible (-SphereCover.Cycles.standardSphereNorthPole (d + 2))
  let := standardSphereOverlap_pathConnectedSpace d
  exact smallMayerVietoris_H1_isZero_of_pathConnected_intersection
    (standardSphere (d + 2)) _ _

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual open-cover comparison for the complements of opposite
sphere poles. Its forward map is induced by inclusion of small chains. -/
def spherePoleHomologyComparison (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    SmallSphereHomology.Cycles.spherePoleSmallHomology v n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E)) n :=
  SmallSingularQuasiIso.Cycles.binarySmallIntegralHomologyIso (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v))
    (SphereCover.Cycles.isOpen_spherePoleOpen v) (SphereCover.Cycles.isOpen_spherePoleOpen (-v))
    (SphereCover.Cycles.spherePoleOpen_union v) n

@[simp]
theorem spherePoleHomologyComparison_hom (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    (spherePoleHomologyComparison v n).hom =
      HomologicalComplex.homologyMap
        (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
          (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v))) n := rfl

/-- The higher-degree shift for ordinary integral singular homology of
standard spheres. The small-chain comparison has been proved, rather
than assumed as a hypothesis. -/
def standardSphereHomologyShift (d n : ℕ) :
    standardSphereHomology (d + 1) (n + 2) ≅ standardSphereHomology d (n + 1) :=
  (spherePoleHomologyComparison (SphereCover.Cycles.standardSphereNorthPole (d + 1)) (n + 2)).symm ≪≫
    SmallSphereHomology.Cycles.standardSphereSmallHomologyShift (d + 1) n

/-- The shift uses the inverse of the actual small-chain inclusion
followed by the established small-chain connecting isomorphism. -/
theorem standardSphereHomologyShift_hom (d n : ℕ) :
    (standardSphereHomologyShift d n).hom =
      (spherePoleHomologyComparison (SphereCover.Cycles.standardSphereNorthPole (d + 1)) (n + 2)).inv ≫
        (SmallSphereHomology.Cycles.standardSphereSmallHomologyShift (d + 1) n).hom := rfl

/-- First homology of the actual unit circle is the integer module. -/
def standardCircleH1Iso : standardSphereHomology 1 1 ≅ ModuleCat.of ℤ ℤ :=
  (spherePoleHomologyComparison (SphereCover.Cycles.standardSphereNorthPole 1) 1).symm ≪≫ SmallCircleHomology.Cycles.smallCircleH1Iso

/-- Ordinary first homology vanishes for every sphere of dimension at
least two. -/
theorem standardSphereH1_isZero (d : ℕ) :
    IsZero (standardSphereHomology (d + 2) 1) :=
  (standardSphereSmallH1_isZero d).of_iso
    (spherePoleHomologyComparison (SphereCover.Cycles.standardSphereNorthPole (d + 2)) 1).symm

/-- Actual integral top homology of a positive-dimensional standard
sphere, computed by induction from the circle. -/
def standardSphereTopHomologyIso (d : ℕ) :
    standardSphereHomology (d + 1) (d + 1) ≅ ModuleCat.of ℤ ℤ := by
  induction d with
  | zero => exact standardCircleH1Iso
  | succ d ih => exact standardSphereHomologyShift (d + 1) d ≪≫ ih

@[simp]
theorem standardSphereTopHomologyIso_zero :
    standardSphereTopHomologyIso 0 = standardCircleH1Iso := rfl

@[simp]
theorem standardSphereTopHomologyIso_succ (d : ℕ) :
    standardSphereTopHomologyIso (d + 1) =
      standardSphereHomologyShift (d + 1) d ≪≫ standardSphereTopHomologyIso d := rfl

/-- The same top-degree isomorphism with a positive dimension supplied
directly rather than as a successor. -/
def standardSphereTopHomologyIsoOfNeZero (d : ℕ) (hd : d ≠ 0) :
    standardSphereHomology d d ≅ ModuleCat.of ℤ ℤ := by
  cases d with
  | zero => exact (hd rfl).elim
  | succ d => exact standardSphereTopHomologyIso d

/-- Every positive-degree group away from the top dimension vanishes in
the actual singular homology of a standard sphere. -/
theorem standardSphereHomology_isZero (d n : ℕ) (hn : n ≠ 0) (hnd : n ≠ d) :
    IsZero (standardSphereHomology d n) := by
  induction d generalizing n with
  | zero => exact standardZeroSphere_higherHomology_isZero n hn
  | succ d ih =>
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          cases n with
          | zero =>
              cases d with
              | zero => exact (hnd rfl).elim
              | succ d => exact standardSphereH1_isZero d
          | succ n =>
              exact (ih (n + 1) (Nat.succ_ne_zero n) (by omega)).of_iso
                (standardSphereHomologyShift d n)

/-- The linear form of the top-degree homology calculation. -/
def standardSphereTopHomologyEquiv (d : ℕ) :
    standardSphereHomology (d + 1) (d + 1) ≃ₗ[ℤ] ℤ :=
  (standardSphereTopHomologyIso d).toLinearEquiv

/-- The top group has rank one over the integers. -/
theorem standardSphereTopHomology_finrank (d : ℕ) :
    Module.finrank ℤ (standardSphereHomology (d + 1) (d + 1)) = 1 := by
  simpa using (standardSphereTopHomologyEquiv d).finrank_eq

/-- A generator fixed by the circle normalization and the specified
inductive connecting isomorphisms. No claim of compatibility with a
separately defined geometric orientation is made here. -/
def standardSphereGenerator (d : ℕ) : standardSphereHomology (d + 1) (d + 1) :=
  (standardSphereTopHomologyEquiv d).symm 1

@[simp]
theorem standardSphereGenerator_normalization (d : ℕ) :
    standardSphereTopHomologyEquiv d (standardSphereGenerator d) = 1 :=
  (standardSphereTopHomologyEquiv d).apply_symm_apply 1

theorem standardSphereGenerator_ne_zero (d : ℕ) : standardSphereGenerator d ≠ 0 := by
  intro h
  have hn := standardSphereGenerator_normalization d
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every top-degree class is a unique integer multiple of the chosen
generator. -/
theorem standardSphereGenerator_generates (d : ℕ)
    (x : standardSphereHomology (d + 1) (d + 1)) :
    ∃! n : ℤ, n • standardSphereGenerator d = x := by
  have hnorm (n : ℤ) :
      standardSphereTopHomologyEquiv d (n • standardSphereGenerator d) = n := by
    calc
      standardSphereTopHomologyEquiv d (n • standardSphereGenerator d) =
          n • standardSphereTopHomologyEquiv d (standardSphereGenerator d) :=
        map_zsmul (standardSphereTopHomologyEquiv d).toLinearMap _ _
      _ = n := by rw [standardSphereGenerator_normalization]; simp
  refine ⟨standardSphereTopHomologyEquiv d x, ?_, ?_⟩
  · apply (standardSphereTopHomologyEquiv d).injective
    exact hnorm _
  · intro n hn
    rw [← hnorm n, hn]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles
