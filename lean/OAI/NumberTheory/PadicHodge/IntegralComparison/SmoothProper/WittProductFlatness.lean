import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.WittFrameProjectionFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.BaseRing
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Products
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex

/-! # Witt Product Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittProductFlatness

noncomputable section

/-! Products with the constructed global Witt frames preserve flatness over the original truncated coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem big_projection (i : StandardCover.Index k X)
    (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
      (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
    (hn : (p : U.ring) ^ (n + 1) = 0)
    (P : BinaryFan U (WittFrameFamily.Family.frame p k X n i).obj) (hP : IsLimit P) : P.fst.ringMap.toRingHom.Flat := by
  let σ := ULift.{u} (StandardCover.coordinateIndex k X i)
  let e : StandardCover.coordinateIndex k X i ≃ σ := Equiv.ulift.symm
  let := Etale.CoordinateReindex.algebra (WittVector p k) (WittFrameFamily.Family.liftRing p k X i)
    (StandardCover.coordinateIndex k X i) σ e
  let := Etale.CoordinateReindex.scalarTower (WittVector p k) (WittFrameFamily.Family.liftRing p k X i)
    (StandardCover.coordinateIndex k X i) σ e
  let := Etale.CoordinateReindex.etale (WittVector p k) (WittFrameFamily.Family.liftRing p k X i)
    (StandardCover.coordinateIndex k X i) σ e
  let j : (Crystalline.Presentation.affineScheme k (StandardCover.coordinateRing k X i)).left ⟶ X.left := StandardCover.chartMap k X i
  let : IsOpenImmersion j := StandardCover.chartMap_open k X i
  exact Open.WittFrameProjectionFlatness.Smooth.projection p k (WittFrameFamily.Family.liftRing p k X i)
    (StandardCover.coordinateRing k X i) σ (WittFrameFamily.Family.reduction p k X i) (WittFrameFamily.Family.reduction_surjective p k X i)
    (WittFrameFamily.Family.reduction_kernel p k X i) (WittFrameFamily.Family.reduction_base p k X i) X j (StandardCover.chartMap_over k X i)
    n U hn P hP

theorem bounded_projection (i : StandardCover.Index k X)
    (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n)
    (P : BinaryFan U (WittFrameFamily.Family.frame p k X n i)) (hP : IsLimit P) : P.fst.hom.ringMap.toRingHom.Flat := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
  exact big_projection p k X n i U.obj U.property (P.map L)
    (BinaryFan.isLimitMapConeEquiv (F := L) (isLimitOfPreserves L hP))

theorem frame_base (i : StandardCover.Index k X) :
    BoundedCrystalline.BaseRing.base (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n i) = WittFrameFamily.Family.coefficientBase p k X n i := by
  apply RingHom.ext
  intro a
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (WittFrameFamily.Family.coefficientBase_mk p k X n i w).symm

theorem frame_flat (i : StandardCover.Index k X) :
    (BoundedCrystalline.BaseRing.base (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n i)).Flat :=
  frame_base p k X n i ▸ WittFrameFamily.Family.flat p k X n i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittProductFlatness
