import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMapBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFreeModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.SemilinearBasisVectors

/-! # Frame Map Vectors -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMapVectors

noncomputable section

/-!
# IntegralComparison: coefficient-vector formula for the actual frame form map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf.Index σ

local instance frameAlgebra : Algebra W (F).obj.ring := (F).obj.base.toAlgebra

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)

theorem map_basis (m : ℕ) (i : Index m) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m (FrameFreeModule.basis p k C σ m i) =
      BoundedEtale.ZeroFormPresheaf.basis p k C σ U m i := by
  have hF : FrameFreeModule.basis p k C σ m i =
      FrameFormBasis.frameBasis p k C σ m
        ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
    FrameFreeModule.basis_apply p k C σ m i
  have hU : BoundedEtale.ZeroFormPresheaf.basis p k C σ U m i =
      BoundedEtale.ZeroFormBasis.basis p k C σ U m
        ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
    Module.Basis.reindex_apply (BoundedEtale.ZeroFormBasis.basis p k C σ U m)
      (Fintype.equivFin (Set.powersetCard σ m)) i
  exact (congrArg (RelativeFrame.FormMap.map H Q π (F).obj τ U m) hF).trans
    ((FrameMapBasis.map_basis p k C σ U m _).trans hU.symm)

theorem map_vectors (m : ℕ) (v : RelativeCrystalline.FreeModule.freeModule Q (Index m) F) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m (FrameFreeModule.linearEquiv p k C σ m v) =
      RelativeCrystalline.FreeModule.linearEquiv H Q π (Index m) U m
        (BoundedEtale.ZeroFormPresheaf.basis p k C σ U m) (fun i => ((τ).app U).ringMap (v i)) := by
  exact SemilinearBasisVectors.map_vectors
    (R := (F).obj.ring) (S := ((H).obj U).ring)
    (M := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (F).obj.ring (F).obj.ideal (F).obj.dividedPowers m)
    (N := RelativeCrystalline.FormData.Forms H Q π U m) ((τ).app U).ringMap.toRingHom
    (RelativeFrame.FormMap.map H Q π (F).obj τ U m).hom.toAddMonoidHom
    (RelativeFrame.FormScalars.map_smul H Q π (F).obj τ U m)
    (FrameFreeModule.basis p k C σ m)
    (BoundedEtale.ZeroFormPresheaf.basis p k C σ U m)
    (map_basis p k C σ U m) v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMapVectors
