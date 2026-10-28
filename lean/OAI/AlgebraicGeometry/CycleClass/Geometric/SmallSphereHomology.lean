import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris
import OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel

/-! # Small Sphere Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology.Cycles

noncomputable section

/-!
# Higher homology of the two-chart small chains of a sphere

The actual Mayer–Vietoris connecting map is an isomorphism in degrees at
least two when the two pieces are contractible. For the complements of
opposite sphere poles, the overlap is homotopy equivalent to a sphere in
one lower ambient dimension. The resulting shift is proved here for the
small singular chain complex itself.

The inclusion of small chains into all singular chains is not assumed to
be a quasi-isomorphism. These results alone do not compute the homology of
all singular chains of a sphere or select an orientation generator.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Vanishing of both summands implies vanishing of the actual middle
homology object in the small-chain Mayer–Vietoris sequence. -/
theorem smallMayerVietorisMiddleHomology_isZero (X : TopCat.{0})
    (U V : Set X) (n : ℕ)
    (hU : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n))
    (hV : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n)) :
    IsZero ((SmallMayerVietoris.Cycles.smallMayerVietorisSequence X U V).X₂.homology n) :=
  ((biprod_isZero_iff _ _).mpr ⟨hU, hV⟩).of_iso
    (SmallMayerVietoris.Cycles.smallMayerVietorisMiddleHomologyIso X U V n)

/-- The actual connecting morphism is an isomorphism when the two
neighboring homology groups of both pieces vanish. -/
def smallMayerVietorisBoundaryIso (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (hUi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) (n + 1)))
    (hVi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) (n + 1)))
    (hUj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n))
    (hVj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n)) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X U V (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (U ∩ V : Set X)) n :=
  (SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X U V).δIso (n + 1) n rfl
    (smallMayerVietorisMiddleHomology_isZero X U V (n + 1) hUi hVi)
    (smallMayerVietorisMiddleHomology_isZero X U V n hUj hVj)

@[simp]
theorem smallMayerVietorisBoundaryIso_hom (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (hUi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) (n + 1)))
    (hVi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) (n + 1)))
    (hUj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n))
    (hVj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n)) :
    (smallMayerVietorisBoundaryIso X U V n hUi hVi hUj hVj).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary X U V n := rfl

/-- For two contractible pieces, the small-chain connecting map is an
isomorphism from degree `n+2` to intersection homology in degree `n+1`. -/
def contractibleSmallMayerVietorisBoundaryIso (X : TopCat.{0}) (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X U V (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (U ∩ V : Set X)) (n + 1) :=
  smallMayerVietorisBoundaryIso X U V (n + 1)
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 2) (by omega))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 2) (by omega))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 1) (Nat.succ_ne_zero n))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 1) (Nat.succ_ne_zero n))

@[simp]
theorem contractibleSmallMayerVietorisBoundaryIso_hom (X : TopCat.{0}) (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    (contractibleSmallMayerVietorisBoundaryIso X U V n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary X U V (n + 1) := rfl

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual singular chains on a sphere that lie in one of the two
complements of the specified opposite poles. -/
abbrev spherePoleSmallChains (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SmallMayerVietoris.Cycles.binarySmallSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v))

/-- The homology of the actual two-chart small chain complex. -/
abbrev spherePoleSmallHomology (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    ModuleCat.{0} ℤ := (spherePoleSmallChains v).homology n

/-- The small-sphere boundary is an isomorphism to the actual homology of
the intersection of the two stereographic domains. -/
def spherePoleSmallBoundaryIso (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    spherePoleSmallHomology v (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of ↥(SphereCover.Cycles.spherePoleOpen v ∩ SphereCover.Cycles.spherePoleOpen (-v))) (n + 1) := by
  letI := SphereCover.Cycles.spherePoleOpen_contractible v
  letI := SphereCover.Cycles.spherePoleOpen_contractible (-v)
  exact contractibleSmallMayerVietorisBoundaryIso _ _ _ n

@[simp]
theorem spherePoleSmallBoundaryIso_hom (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    (spherePoleSmallBoundaryIso v n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
        (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v)) (n + 1) := rfl

/-- The higher small-chain homology of a sphere shifts to the actual
singular homology of its equatorial sphere. -/
def spherePoleSmallHomologyShift (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    spherePoleSmallHomology v (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (SphereCover.Cycles.SphereEquatorSpace v))) (n + 1) :=
  spherePoleSmallBoundaryIso v n ≪≫
    ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
      (X := TopCat.of ↥(SphereCover.Cycles.spherePoleOpen v ∩ SphereCover.Cycles.spherePoleOpen (-v)))
      (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere (SphereCover.Cycles.SphereEquatorSpace v)))
      (SphereCover.Cycles.spherePoleIntersectionSphereEquiv v) (n + 1)

/-- The shift is specifically the connecting morphism followed by the
map from the established stereographic and radial homotopy equivalence. -/
theorem spherePoleSmallHomologyShift_hom (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    (spherePoleSmallHomologyShift v n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
        (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v)) (n + 1) ≫
      RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom (SphereCover.Cycles.spherePoleIntersectionSphereEquiv v).toFun) (n + 1) := rfl

/-- For the standard `d`-sphere and the specified opposite-pole cover,
the actual small-chain homology in degree `n+2` is isomorphic to the
homology in degree `n+1` of the unit sphere in `ℝ^d`. -/
def standardSphereSmallHomologyShift (d n : ℕ) :
    spherePoleSmallHomology (SphereCover.Cycles.standardSphereNorthPole d) (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin d)))) (n + 1) :=
  spherePoleSmallBoundaryIso (SphereCover.Cycles.standardSphereNorthPole d) n ≪≫
    ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
      (X := TopCat.of ↥(SphereCover.Cycles.spherePoleOpen (SphereCover.Cycles.standardSphereNorthPole d) ∩
        SphereCover.Cycles.spherePoleOpen (-SphereCover.Cycles.standardSphereNorthPole d)))
      (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin d))))
      (SphereCover.Cycles.standardSphereOverlapEquiv d) (n + 1)

@[simp]
theorem standardSphereSmallHomologyShift_hom (d n : ℕ) :
    (standardSphereSmallHomologyShift d n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (d + 1)))))
        (SphereCover.Cycles.spherePoleOpen (SphereCover.Cycles.standardSphereNorthPole d))
        (SphereCover.Cycles.spherePoleOpen (-SphereCover.Cycles.standardSphereNorthPole d)) (n + 1) ≫
      RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom (SphereCover.Cycles.standardSphereOverlapEquiv d).toFun) (n + 1) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology.Cycles
