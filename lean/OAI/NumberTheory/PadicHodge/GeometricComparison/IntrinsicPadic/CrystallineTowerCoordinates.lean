import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BoundedExtTower
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpSequence
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseTransitionCoordinates

/-! # Crystalline Tower Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates

noncomputable section

/-! The direct original Ext-restriction tower is the original
crystalline resolution inverse sequence in identity coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def original : ℕᵒᵖ ⥤ ModuleCat.{2} R :=
  IntegralComparison.Crystalline.FiniteInverseLimit.diagram (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1

theorem successor (n : ℕ) : (BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram p Y).map (homOfLE (Nat.le_succ n)).op =
    (original p Y).map (homOfLE (Nat.le_succ n)).op := by
  simp only [BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram, original, IntegralComparison.Crystalline.FiniteInverseLimit.diagram,
    IntegralComparison.SequentialKernelLimit.diagram, Functor.ofOpSequence_map_homOfLE_succ]
  exact congrArg ModuleCat.ofHom (IntegralComparison.Crystalline.InverseTransitionCoordinates.transition w n 1).symm

def iso : BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram p Y ≅ original p Y :=
  OpSequence.OpSequenceIso.iso _ _ (fun _ => Iso.refl _) (fun n => by
    exact (Category.comp_id ((BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram p Y).map (homOfLE (Nat.le_succ n)).op)).trans
      ((successor p Y n).trans ((Category.id_comp ((original p Y).map (homOfLE (Nat.le_succ n)).op)).symm)))

def limitIso : limit (BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram p Y) ≅ limit (original p Y) :=
  (lim (C := ModuleCat.{2} R)).mapIso (iso p Y)

theorem limitIso_hom_π (n : ℕ) :
    (limitIso p Y).hom ≫ limit.π (original p Y) (op n) =
      limit.π (BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram p Y) (op n) := by
  change limMap (iso p Y).hom ≫ limit.π (original p Y) (op n) = _
  rw [limMap_π]
  exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates
