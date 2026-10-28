import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.DifferenceNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineCoverIntersections

/-! # Cech Cycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.CechCycle

noncomputable section

/-! The constructed base-tangent lifts give a linear Cech cocycle
on the actual affine cover of the fixed fiber. The triple-intersection
equation uses the original fixed-fiber restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [IsSeparated X.hom]
    (U : X.left.AffineOpenCover)

attribute [local implicit_reducible] Family.AffineCoverIntersections.familyCoverAffineOpen Family.AffineCoverIntersections.familyCoverPairAffineOpen Family.AffineCoverIntersections.familyCoverTripleAffineOpen

abbrev fixedFamilyCechOneCochains := ∀ i j : U.I₀,
  Derivation k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
    (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))

abbrev fixedFamilyCechTwoCochains := ∀ i j l : U.I₀,
  Derivation k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l))
    (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l))

def fixedFamilyCechDifferentialOne :
    fixedFamilyCechOneCochains k R X U →ₗ[k] fixedFamilyCechTwoCochains k R X U where
  toFun a i j l :=
    FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from
        inf_le_left) (a i j) +
    FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U j l).1 from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a j l) -
    FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i l).1 from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a i l)
  map_add' a b := by
    funext i j l
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c a := by
    funext i j l
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, smul_sub]

variable [Smooth X.hom]

def familyTangentPair (i j : U.I₀) : Derivation k R k →ₗ[k]
    Derivation k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j))
      (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)) :=
  Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference k R X (V := Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j)
    (W := Family.AffineCoverIntersections.familyCoverAffineOpen R X U i) (Z := Family.AffineCoverIntersections.familyCoverAffineOpen R X U j) inf_le_left inf_le_right

theorem familyTangentPair_restricted_cocycle (i j l : U.I₀) :
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i j).1 from
        inf_le_left)).comp (familyTangentPair k R X U i j) +
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U j l).1 from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right)).comp (familyTangentPair k R X U j l) =
    (FixedFiber.DerivationPresheaf.fixedFiberDerivationRestriction R k X
      (show (Family.AffineCoverIntersections.familyCoverTripleAffineOpen R X U i j l).1 ≤ (Family.AffineCoverIntersections.familyCoverPairAffineOpen R X U i l).1 from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)).comp (familyTangentPair k R X U i l) := by
  unfold familyTangentPair
  rw [DifferenceNaturality.familyCommonOpenTangentDifference_restrict, DifferenceNaturality.familyCommonOpenTangentDifference_restrict,
    DifferenceNaturality.familyCommonOpenTangentDifference_restrict]
  exact Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference_cocycle k R X _ _ _

def familyTangentCechCochain : Derivation k R k →ₗ[k] fixedFamilyCechOneCochains k R X U :=
  LinearMap.pi (fun i => LinearMap.pi (fun j => familyTangentPair k R X U i j))

theorem familyTangentCechCochain_isCycle (d : Derivation k R k) :
    fixedFamilyCechDifferentialOne k R X U (familyTangentCechCochain k R X U d) = 0 := by
  funext i j l
  exact sub_eq_zero.mpr (LinearMap.congr_fun (familyTangentPair_restricted_cocycle k R X U i j l) d)

def familyTangentCechCycle : Derivation k R k →ₗ[k] (fixedFamilyCechDifferentialOne k R X U).ker :=
  (familyTangentCechCochain k R X U).codRestrict (fixedFamilyCechDifferentialOne k R X U).ker
    (familyTangentCechCochain_isCycle k R X U)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.CechCycle
