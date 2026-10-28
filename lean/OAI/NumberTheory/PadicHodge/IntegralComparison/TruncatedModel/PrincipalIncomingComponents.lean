import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedComponents

/-! # Principal Incoming Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingComponents.Map

noncomputable section

/-! Principal-open coordinates for the exact factorization of the
original global comparison through its fixed incoming crystalline frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem precompose_components {C : Type*} [Category C] {K L A B D E F Q : C}
    (u : K ⟶ L) (v : L ⟶ A) (a : A ⟶ B) (b : B ⟶ D) (e : D ⟶ F)
    (c : L ⟶ E) (r : B ⟶ E) (t : E ⟶ Q) (j : Q ⟶ F)
    (hc : c = (v ≫ a) ≫ r) (hb : b ≫ e = (r ≫ t) ≫ j) :
    (u ≫ v ≫ (a ≫ b)) ≫ e = ((u ≫ c) ≫ t) ≫ j := by
  rw [hc]
  simp only [Category.assoc] at hb ⊢
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

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local instance] PrincipalIncomingBase.Map.globalSeparated PrincipalIncomingBase.Map.globalCoproducts PrincipalIncomingBase.Map.localCoproducts

variable (q : ℕ) (r : (PrincipalFrame.Index X.left V)ᵒᵖ)

abbrev diagonal_component :=
  congrArg (fun a => (a.f q).app r)
    (PrincipalFactorization.native_factorization p k n X Y f hp V J)

theorem factorization_component :
    ((Principal.Comparison.map p k n X Y f hp V J ≫
      ((NatIso.mapHomologicalComplex e (.up ℕ)).app J.cocomplex).hom).f q).app r =
      ((PrincipalIncomingBase.Map.viaIncoming p k n X Y f hp V J).f q).app r :=
  precompose_components
    (((Principal.Comparison.coefficientMap p k n X Y f hp V).f q).app r)
    ((((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (Functor.op F) (𝟭 (ModuleCat.{2} R)) (.up ℕ)
      (FrameDiagonalMap.source p k n X Y f hp)).inv).f q).app r)
    (((((H).mapHomologicalComplex (.up ℕ)).map (FrameDiagonalMap.map p k n X Y f hp)).f q).app r)
    (((((H).mapHomologicalComplex (.up ℕ)).map (DiagonalCech.Comparison.map p k n X Y f hp J)).f q).app r)
    (((((NatIso.mapHomologicalComplex e (.up ℕ)).app J.cocomplex).hom).f q).app r)
    (((PrincipalFixedConeCoordinates.localMap p k n X Y f hp V).f q).app r)
    (((PrincipalFrameSections.inverse p k n X Y f hp V).f q).app r)
    (((((NatIso.mapHomologicalComplex e (.up ℕ)).app ((P).obj (op V))).hom).f q).app r)
    (((((T).mapHomologicalComplex (.up ℕ)).map (Incoming.Comparison.map p k n X Y f hp V J)).f q).app r)
    (PrincipalFixedComponents.coordinates p k n X Y f hp V q r)
    (diagonal_component p k n X Y f hp V J q r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIncomingComponents.Map
