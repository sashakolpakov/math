import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMapBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFreeModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.SemilinearBasisVectors

/-! # Frame Map Vectors -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMapVectors

noncomputable section

/-!
# IntegralComparison: coefficient-vector formula for the actual frame form map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  BoundedSmooth.WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "Index" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf.Index σ

local instance frameAlgebra : Algebra W (F).obj.ring := (F).obj.base.toAlgebra

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

theorem map_basis (m : ℕ) (i : Index m) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m (FrameFreeModule.basis p k A C σ ρ hρ hker hbase n m i) =
      BoundedSmooth.WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n U m i := by
  have hF : FrameFreeModule.basis p k A C σ ρ hρ hker hbase n m i =
      FrameFormBasis.frameBasis p k A σ n C ρ hρ hker hbase m
        ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
    FrameFreeModule.basis_apply p k A C σ ρ hρ hker hbase n m i
  have hU : BoundedSmooth.WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n U m i =
      BoundedSmooth.WittFormBasis.basis p k A C σ ρ hρ hker hbase n U m
        ((Fintype.equivFin (Set.powersetCard σ m)).symm i) :=
    Module.Basis.reindex_apply (BoundedSmooth.WittFormBasis.basis p k A C σ ρ hρ hker hbase n U m)
      (Fintype.equivFin (Set.powersetCard σ m)) i
  exact (congrArg (RelativeFrame.FormMap.map H Q π (F).obj τ U m) hF).trans
    ((FrameMapBasis.map_basis p k A C σ ρ hρ hker hbase n U m _).trans hU.symm)

theorem map_vectors (m : ℕ) (v : RelativeCrystalline.FreeModule.freeModule Q (Index m) F) :
    RelativeFrame.FormMap.map H Q π (F).obj τ U m (FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m v) =
      RelativeCrystalline.FreeModule.linearEquiv H Q π (Index m) U m
        (BoundedSmooth.WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n U m) (fun i => ((τ).app U).ringMap (v i)) := by
  exact SemilinearBasisVectors.map_vectors
    (R := (F).obj.ring) (S := ((H).obj U).ring)
    (M := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (F).obj.ring (F).obj.ideal (F).obj.dividedPowers m)
    (N := RelativeCrystalline.FormData.Forms H Q π U m) ((τ).app U).ringMap.toRingHom
    (RelativeFrame.FormMap.map H Q π (F).obj τ U m).hom.toAddMonoidHom
    (RelativeFrame.FormScalars.map_smul H Q π (F).obj τ U m)
    (FrameFreeModule.basis p k A C σ ρ hρ hker hbase n m)
    (BoundedSmooth.WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n U m)
    (map_basis p k A C σ ρ hρ hker hbase n U m) v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMapVectors
