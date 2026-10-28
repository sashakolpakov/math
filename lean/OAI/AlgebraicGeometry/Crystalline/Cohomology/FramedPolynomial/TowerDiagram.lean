import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimitUniversal

/-! # Tower Diagram -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram

noncomputable section

/-!
# The native framed tower has the actual quotient transition maps

The unique coordinate-preserving transition maps agree with the original
p-power quotient maps of the PD envelope. Hence the diagram of actual
ambient functions on the framed tower is the module diagram of the
existing PD-envelope inverse system.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "A" => MvPolynomial σ W
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hbase
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ (fun i => r (MvPolynomial.X i))
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B A r hr hbase

def quotientTransition {m n : ℕ} (h : m ≤ n) : L m ⟶ L n where
  hom :=
    { ambientMap := ((D).map (homOfLE h).op).hom
      reducedMap := AlgHom.id k B
      reduction_comm x := DFunLike.congr_fun ((D).map (homOfLE h).op).reduction_comp x
      over_X := by
        change Spec.map (𝟙 (CommRingCat.of B)) ≫ 𝟙 _ = 𝟙 _
        rw [Spec.map_id, Category.id_comp]
      dp_comp := ((D).map (homOfLE h).op).dp_comp }
  coordinate_comm _ := rfl

theorem transition_eq {m n : ℕ} (h : m ≤ n) :
    Tower.FramedPolynomialTower.transition p k B σ r hr hbase h = quotientTransition p k B σ r hr hbase h :=
  Subsingleton.elim _ _

def functions : ℕᵒᵖ ⥤ ModuleCat.{u} W :=
  (T).op ⋙ (U).op ⋙ Site.functions p k X

def diagramIso : functions p k B σ r hr hbase ≅ D ⋙ PD.InverseLimitUniversal.PDInverseLimitUniversal.ambientModules p k B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    have he := congrArg (fun g => g.hom.ambientMap.toLinearMap)
      (transition_eq p k B σ r hr hbase (leOfHom f.unop))
    exact ModuleCat.hom_ext he)

def limitIso : limit (functions p k B σ r hr hbase) ≅ ModuleCat.of W (PD.InverseLimit.PDInverseLimit.Ring p k B D) :=
  HasLimit.isoOfNatIso (diagramIso p k B σ r hr hbase) ≪≫ (PD.InverseLimitUniversal.PDInverseLimitUniversal.limitIso p k B D).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram
