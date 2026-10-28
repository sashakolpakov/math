import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpSequence
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimits
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BoundedExtTower
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientLimit

/-! # Principal Tower -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalTower.IntrinsicPadicPrincipalTower

noncomputable section

/-! The principal-quotient comparison is an isomorphism of the actual
inverse diagrams and therefore of their categorical limits. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

def sourceDiagram : ℕᵒᵖ ⥤ ModuleCat.{2} R :=
  CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram ℤ_[p] K (p : ℤ_[p]) 1 ⋙ F

def targetDiagram : ℕᵒᵖ ⥤ ModuleCat.{2} R :=
  BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram p Y

omit [X.left.IsSeparated] in
theorem source_successor (n : ℕ) : (sourceDiagram p X).map (homOfLE (Nat.le_succ n)).op =
    PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.sourceMap p X n (n + 1) (Nat.le_succ n) := by
  simp only [sourceDiagram, CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram, IntegralComparison.SequentialKernelLimit.diagram,
    Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

omit [IsSeparated Y.hom] in
theorem target_successor (n : ℕ) : (targetDiagram p Y).map (homOfLE (Nat.le_succ n)).op =
    ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map w n (n + 1) (Nat.le_succ n) 1) := by
  simp only [targetDiagram, BoundedExtTower.IntrinsicPadicBoundedExtTower.diagram, IntegralComparison.SequentialKernelLimit.diagram,
    Functor.ofOpSequence_map_homOfLE_succ]
  rfl

theorem successor (n : ℕ) : (sourceDiagram p X).map (homOfLE (Nat.le_succ n)).op ≫
    (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom =
      (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I (n + 1)).hom ≫
        (targetDiagram p Y).map (homOfLE (Nat.le_succ n)).op := by
  exact (congrArg (fun a => a ≫ (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom)
    (source_successor p X n)).trans
      ((PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.natural p X Y f hp I n (n + 1) (Nat.le_succ n)).trans
        (congrArg (fun a => (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I (n + 1)).hom ≫ a)
          (target_successor p Y n).symm))

def diagramIso : sourceDiagram p X ≅ targetDiagram p Y :=
  OpSequence.OpSequenceIso.iso (sourceDiagram p X) (targetDiagram p Y)
    (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I) (successor p X Y f hp I)

def limitIso : (F).obj (limit (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram ℤ_[p] K (p : ℤ_[p]) 1)) ≅
    limit (targetDiagram p Y) :=
  CoefficientLimit.IntrinsicPadicCoefficientLimitComparison.iso p
    (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram ℤ_[p] K (p : ℤ_[p]) 1)
    (targetDiagram p Y) (diagramIso p X Y f hp I)

theorem limitIso_π (n : ℕ) : (limitIso p X Y f hp I).hom ≫ limit.π (targetDiagram p Y) (op n) =
    (F).map (limit.π (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram ℤ_[p] K (p : ℤ_[p]) 1) (op n)) ≫
      (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom :=
  CoefficientLimit.IntrinsicPadicCoefficientLimitComparison.hom_π p
    (CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram ℤ_[p] K (p : ℤ_[p]) 1)
    (targetDiagram p Y) (diagramIso p X Y f hp I) (op n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalTower.IntrinsicPadicPrincipalTower
