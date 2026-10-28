import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFactorizationData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors

/-! # Principal Diagram Factorization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalDiagramFactorization

noncomputable section

/-! The native section functors factor an arbitrary frame diagram
through the fixed incoming subsite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (V : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors.sections p k n X Y f
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors.principalRestriction p k n X V
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors.incomingRestriction p k n X Y f V
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFunctors.localSections p k n X Y f V

local instance globalCoproducts : HasCoproducts.{0} A :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedCrystalline.Site.topology w n)

local instance localCoproducts : HasCoproducts.{0}
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
      w (f ⁻¹ᵁ V.val).ι n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedOpen.Subsite.topology w (f ⁻¹ᵁ V.val).ι n)

omit [Fintype k] [IsSeparated Y.hom] in
theorem comparison (P : X.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ)
    (hF : ∀ Z : X.left.affineOpens, IsIso (((F).mapHomologicalComplex (.up ℕ)).map
      (P.map (homOfLE (inf_le_left : Z ⊓ V ≤ Z)).op)))
    (M : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ)
    (η : (Functor.const X.left.affineOpensᵒᵖ).obj M ⟶ P ⋙ (S).mapHomologicalComplex (.up ℕ))
    {K L : CochainComplex A ℕ} (c : K ≅ GeometricComparison.CechCone.Total.CechConeTotal.total U P) (b : K ⟶ L) :
    ((H).mapHomologicalComplex (.up ℕ)).map
        ((GeometricComparison.CechCone.Realization.CechConeRealization.map S U P M η ≫ ((S).mapHomologicalComplex (.up ℕ)).map c.inv) ≫
          ((S).mapHomologicalComplex (.up ℕ)).map b) ≫
      ((NatIso.mapHomologicalComplex (PrincipalFunctors.iso p k n X Y f V) (.up ℕ)).app L).hom =
    (((H).mapHomologicalComplex (.up ℕ)).map (η.app (op V)) ≫
        ((NatIso.mapHomologicalComplex (PrincipalFunctors.iso p k n X Y f V) (.up ℕ)).app
          (P.obj (op V))).hom) ≫
      ((T).mapHomologicalComplex (.up ℕ)).map
        ((GeometricComparison.Semilattice.MappedChartTotal.SemilatticeMappedChartTotal.map X.left.affineOpens U V F P hF ≫
          ((F).mapHomologicalComplex (.up ℕ)).map c.inv) ≫ ((F).mapHomologicalComplex (.up ℕ)).map b) :=
  PrincipalFactorizationData.comparison p k n X Y f V S H F T
    (PrincipalFunctors.iso p k n X Y f V) P hF M η c b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalDiagramFactorization
