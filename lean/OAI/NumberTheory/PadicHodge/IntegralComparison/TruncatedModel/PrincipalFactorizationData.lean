import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Restricted

/-! # Principal Factorization Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFactorizationData

noncomputable section

/-! Principal-open restriction factors arbitrary coefficient diagrams
through the fixed incoming subsite, before choosing a native resolution. -/

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

local instance globalCoproducts : HasCoproducts.{0} A :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedCrystalline.Site.topology w n)
local instance localCoproducts : HasCoproducts.{0}
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
      w (f ⁻¹ᵁ V.val).ι n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts R (BoundedOpen.Subsite.topology w (f ⁻¹ᵁ V.val).ι n)

abbrev comparison (S : A ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) [S.Additive]
    (H : (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
      (PrincipalFrame.Index X.left V)ᵒᵖ ⥤ ModuleCat.{2} R) [H.Additive]
    (F : A ⥤ BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
      w (f ⁻¹ᵁ V.val).ι n) [F.Additive]
    (T : BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
      w (f ⁻¹ᵁ V.val).ι n ⥤ (PrincipalFrame.Index X.left V)ᵒᵖ ⥤ ModuleCat.{2} R) [T.Additive]
    (e : S ⋙ H ≅ F ⋙ T)
    (P : X.left.affineOpensᵒᵖ ⥤ CochainComplex A ℕ)
    (hF : ∀ Z : X.left.affineOpens, IsIso (((F).mapHomologicalComplex (.up ℕ)).map
      (P.map (homOfLE (inf_le_left : Z ⊓ V ≤ Z)).op)))
    (M : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ)
    (η : (Functor.const X.left.affineOpensᵒᵖ).obj M ⟶ P ⋙ (S).mapHomologicalComplex (.up ℕ))
    {K L : CochainComplex A ℕ} (c : K ≅ GeometricComparison.CechCone.Total.CechConeTotal.total U P) (b : K ⟶ L) :=
  GeometricComparison.CechCone.Restricted.CechConeRestrictedComparison.comparison X.left.affineOpens U V S H F T e P hF M η c b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFactorizationData
