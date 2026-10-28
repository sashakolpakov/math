import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualAffineIntersections

/-! # Common Open Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenCocycle

noncomputable section

/-! On literal common affine opens, the actual normalized chart
transitions give an additive derivation cocycle. Separatedness supplies
the actual pairwise and triple affine intersections of the chosen cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k)))) [Smooth X.hom]
    (U : X.left.AffineOpenCover) (V : X.left.affineOpens)

theorem dualCommonOpenDerivation_cocycle (i j l : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange)
    (hl : V.1 ≤ (U.f l).opensRange) :
    CommonOpenDerivation.dualCommonOpenDerivation k X U V i j hi hj + CommonOpenDerivation.dualCommonOpenDerivation k X U V j l hj hl =
      CommonOpenDerivation.dualCommonOpenDerivation k X U V i l hi hl := by
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction k)
  have hcomp : G.map ((DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj ≪≫
      DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 j l hj hl).hom) = 𝟙 _ := by
    rw [DualOpen.CommonTransitions.dualCommonOpenTransition_cocycle]
    exact DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i l hi hl
  have hd := AffineProduct.DerivationLaws.affineProductTransitionDerivation_trans k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj) (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 j l hj hl)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 j l hj hl) hcomp
  exact hd.symm.trans (AffineProduct.DerivationLaws.affineProductTransitionDerivation_congr k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    _ _ hcomp (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i l hi hl)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_cocycle k X U V.1 i j l hi hj hl))

theorem dualCommonOpenDerivation_eq_zero_iff (i j : U.I₀)
    (hi : V.1 ≤ (U.f i).opensRange) (hj : V.1 ≤ (U.f j).opensRange) :
    CommonOpenDerivation.dualCommonOpenDerivation k X U V i j hi hj = 0 ↔
      DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj = Iso.refl _ :=
  AffineProduct.DerivationLaws.affineProductTransitionDerivation_eq_zero_iff k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)
    (DualOpen.CommonTransitions.dualCommonOpenTransition k X U V.1 i j hi hj)
    (DualOpen.CommonTransitions.dualCommonOpenTransition_reduction k X U V.1 i j hi hj)

variable [IsSeparated X.hom]

def dualFamilyPairAffineOpen (i j : U.I₀) : X.left.affineOpens :=
  ⟨(U.f i).opensRange ⊓ (U.f j).opensRange,
    VaryingDualAffineIntersections.varyingDualFamily_affineIntersection k X _ _
      (isAffineOpen_opensRange (U.f i)) (isAffineOpen_opensRange (U.f j))⟩

def dualFamilyTripleAffineOpen (i j l : U.I₀) : X.left.affineOpens :=
  ⟨(dualFamilyPairAffineOpen k X U i j).1 ⊓ (U.f l).opensRange,
    VaryingDualAffineIntersections.varyingDualFamily_affineIntersection k X _ _
      (dualFamilyPairAffineOpen k X U i j).2 (isAffineOpen_opensRange (U.f l))⟩

def dualFamilyPairTransitionDerivation (i j : U.I₀) :=
  CommonOpenDerivation.dualCommonOpenDerivation k X U (dualFamilyPairAffineOpen k X U i j) i j inf_le_left inf_le_right

theorem dualFamilyTripleTransition_cocycle (i j l : U.I₀) :
    CommonOpenDerivation.dualCommonOpenDerivation k X U (dualFamilyTripleAffineOpen k X U i j l) i j
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
      CommonOpenDerivation.dualCommonOpenDerivation k X U (dualFamilyTripleAffineOpen k X U i j l) j l
        (inf_le_left.trans inf_le_right) inf_le_right =
      CommonOpenDerivation.dualCommonOpenDerivation k X U (dualFamilyTripleAffineOpen k X U i j l) i l
        (inf_le_left.trans inf_le_left) inf_le_right :=
  dualCommonOpenDerivation_cocycle k X U (dualFamilyTripleAffineOpen k X U i j l) i j l
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenCocycle
