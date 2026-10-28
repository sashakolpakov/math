import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Incoming
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFactorization

/-! # Principal Incoming Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingBase.Map

noncomputable section

/-! The original principal PD comparison expressed through the fixed
incoming frame and its augmentation-preserving injective comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem precompose {A D : Type*} [Category A] [Category D] (F : A ⥤ D)
    {X Y Z : A} {L M N P Q : D}
    (u : L ⟶ M) (v : M ⟶ F.obj X) (a : X ⟶ Y) (b : Y ⟶ Z)
    (e : F.obj Z ⟶ N) (c : M ⟶ P) (r : F.obj Y ⟶ P) (t : P ⟶ Q) (j : Q ⟶ N)
    (hb : F.map b ≫ e = (r ≫ t) ≫ j) (hc : c = (v ≫ F.map a) ≫ r) :
    (u ≫ v ≫ F.map (a ≫ b)) ≫ e = ((u ≫ c) ≫ t) ≫ j := by
  rw [hc]
  simp only [Functor.map_comp, Category.assoc] at hb ⊢
  rw [hb]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X V
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.localSections p k n X Y f V
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.iso p k n X Y f V
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left V.val V.property

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance globalCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedCrystalline.Site.topology w n)

local instance localCoproducts : HasCoproducts.{0}
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w (f ⁻¹ᵁ V.val).ι n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedOpen.Subsite.topology w (f ⁻¹ᵁ V.val).ι n)

def localSource := Principal.Comparison.coefficientMap p k n X Y f hp V ≫
  PrincipalFixedConeCoordinates.localMap p k n X Y f hp V

def localMap := localSource p k n X Y f hp V ≫
  ((NatIso.mapHomologicalComplex e (.up ℕ)).app ((P).obj (op V))).hom

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def viaIncoming := localMap p k n X Y f hp V ≫
  ((T).mapHomologicalComplex (.up ℕ)).map (Incoming.Comparison.map p k n X Y f hp V J)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingBase.Map
