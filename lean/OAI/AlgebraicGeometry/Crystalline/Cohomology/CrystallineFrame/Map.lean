import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Lifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps

/-! # Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Map.CrystallineFrameMap

noncomputable section

/-!
# Native crystalline maps for polynomial frame linearization

The divided coordinates at an object measure displacement from chosen
lifts of fixed residue coordinates. Morphisms translate these divided
coordinates by the discrepancy of the lifts. They preserve the actual
PD structures and reductions, and preserve the total frame coordinates.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

abbrev object := PolynomialFunctor.CrystallinePolynomialFunctor.object p k X σ

variable {p k B σ}
variable {Q P U : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}

def ambientMap (f : Q ⟶ P) : (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) →ₐ[W]
    (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) := by
  have ht (w : W) := IsScalarTower.algebraMap_apply W Q.thickening.ring
    (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) w
  letI : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  let g := Divided.AffineMaps.DividedAffineMaps.map P.thickening.ring Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (Lifts.CrystallineFrameLifts.translation a f) (Lifts.CrystallineFrameLifts.translation_mem a f)
  refine { __ := g.toRingHom, commutes' := ?_ }
  intro w
  change g (algebraMap W (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) w) = _
  rw [IsScalarTower.algebraMap_apply W P.thickening.ring _, Divided.AffineMaps.DividedAffineMaps.map_coefficient]
  have hc : algebraMap P.thickening.ring Q.thickening.ring (algebraMap W P.thickening.ring w) =
      algebraMap W Q.thickening.ring w := f.ambientMap.commutes w
  rw [hc]
  exact (ht w).symm

theorem ambientMap_coefficient (f : Q ⟶ P) (t : P.thickening.ring) :
    CrystallineFrameMap.ambientMap a f (algebraMap P.thickening.ring (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) t) =
      algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) (f.ambientMap t) := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  exact Divided.AffineMaps.DividedAffineMaps.map_coefficient P.thickening.ring Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (Lifts.CrystallineFrameLifts.translation a f) (Lifts.CrystallineFrameLifts.translation_mem a f) t

theorem ambientMap_coordinate (f : Q ⟶ P) (i : σ) :
    CrystallineFrameMap.ambientMap a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ 1 i) =
      algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
        (Lifts.CrystallineFrameLifts.translation a f i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  exact Divided.AffineMaps.DividedAffineMaps.map_coordinate P.thickening.ring Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (Lifts.CrystallineFrameLifts.translation a f) (Lifts.CrystallineFrameLifts.translation_mem a f) i

theorem ambientMap_relativePD (f : Q ⟶ P) :
    DividedPowers.IsDPMorphism
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers P.thickening.ring σ
        (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
        (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
      (CrystallineFrameMap.ambientMap a f).toRingHom := by
  let : Algebra P.thickening.ring Q.thickening.ring := f.ambientMap.toRingHom.toAlgebra
  exact Divided.AffineMaps.DividedAffineMaps.map_isDPMorphism P.thickening.ring Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (Lifts.CrystallineFrameLifts.translation a f) (Lifts.CrystallineFrameLifts.translation_mem a f)
    (RingHom.ker P.thickening.reduction) P.thickening.dividedPowers f.dp_comp

theorem ambientMap_isDPMorphism (f : Q ⟶ P) :
    DividedPowers.IsDPMorphism (object p k B σ P).thickening.dividedPowers
      (object p k B σ Q).thickening.dividedPowers (CrystallineFrameMap.ambientMap a f).toRingHom :=
  (PolynomialThickening.CrystallinePolynomialThickening.identity_isDPMorphism p k Q.residueRing σ Q.thickening).comp _
    ((ambientMap_relativePD a f).comp _ (PolynomialThickening.CrystallinePolynomialThickening.identity_inverse_isDPMorphism
      p k P.residueRing σ P.thickening))

theorem reduction_coefficient (Q : Site.Object p k X) (t : Q.thickening.ring) :
    (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening)
      (algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) t) = Q.thickening.reduction t :=
  DFunLike.congr_fun (PolynomialThickening.CrystallinePolynomialThickening.inclusion p k Q.residueRing σ Q.thickening).reduction_comp t

theorem generator_mem (Q : Site.Object p k X) (n : ℕ) (hn : n ≠ 0) (i : σ) :
    Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ n i ∈ RingHom.ker (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening) := by
  rw [PolynomialThickening.CrystallinePolynomialThickening.reduction_kernel]
  exact Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) i n hn

theorem reduction_ambientMap (f : Q ⟶ P) (t : (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring))) :
    (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening) (CrystallineFrameMap.ambientMap a f t) =
      f.reducedMap ((PolynomialThickening.CrystallinePolynomialThickening.reduction p k P.residueRing σ P.thickening) t) := by
  have he : (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening).comp (CrystallineFrameMap.ambientMap a f).toRingHom =
      f.reducedMap.toRingHom.comp (PolynomialThickening.CrystallinePolynomialThickening.reduction p k P.residueRing σ P.thickening) := by
    apply FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext P.thickening.ring σ
    · intro t
      change (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening)
        (CrystallineFrameMap.ambientMap a f (algebraMap P.thickening.ring (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) t)) =
          f.reducedMap ((PolynomialThickening.CrystallinePolynomialThickening.reduction p k P.residueRing σ P.thickening)
            (algebraMap P.thickening.ring (DividedPowerAlgebra P.thickening.ring (σ →₀ P.thickening.ring)) t))
      rw [ambientMap_coefficient, reduction_coefficient, reduction_coefficient]
      exact f.reduction_comm t
    · intro n i
      change (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening) (CrystallineFrameMap.ambientMap a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i)) =
        f.reducedMap ((PolynomialThickening.CrystallinePolynomialThickening.reduction p k P.residueRing σ P.thickening) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i))
      by_cases hn : n = 0
      · subst n
        simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator, DividedPowerAlgebra.dp_zero, map_one]
      · have hP := generator_mem P n hn i
        have hQ := (ambientMap_isDPMorphism a f).ideal_comp
          (Ideal.mem_map_of_mem (CrystallineFrameMap.ambientMap a f).toRingHom hP)
        change (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening) (CrystallineFrameMap.ambientMap a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i)) =
          f.reducedMap ((PolynomialThickening.CrystallinePolynomialThickening.reduction p k P.residueRing σ P.thickening) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i))
        change (PolynomialThickening.CrystallinePolynomialThickening.reduction p k P.residueRing σ P.thickening) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i) = 0 at hP
        change (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening) (CrystallineFrameMap.ambientMap a f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator P.thickening.ring σ n i)) = 0 at hQ
        rw [hQ, hP]
        exact (map_zero f.reducedMap).symm
  exact RingHom.congr_fun he t

def map (f : Q ⟶ P) : object p k B σ Q ⟶ object p k B σ P where
  reducedMap := f.reducedMap
  ambientMap := CrystallineFrameMap.ambientMap a f
  reduction_comm := reduction_ambientMap a f
  over_X := f.over_X
  dp_comp := ambientMap_isDPMorphism a f

def coordinate (Q : Site.Object p k X) (i : σ) : (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) :=
  algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
    (Lifts.CrystallineFrameLifts.lift p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i

theorem coordinate_naturality (f : Q ⟶ P) (i : σ) :
    CrystallineFrameMap.ambientMap a f (coordinate a P i) = coordinate a Q i := by
  rw [coordinate, map_add, ambientMap_coefficient, ambientMap_coordinate, coordinate]
  change algebraMap Q.thickening.ring _ (f.ambientMap (Lifts.CrystallineFrameLifts.lift p k B σ a P i)) +
    (algebraMap Q.thickening.ring _ (Lifts.CrystallineFrameLifts.lift p k B σ a Q i -
      f.ambientMap (Lifts.CrystallineFrameLifts.lift p k B σ a P i)) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i) = _
  rw [map_sub, ← add_assoc, ← add_sub_assoc, add_sub_cancel_left]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Map.CrystallineFrameMap
