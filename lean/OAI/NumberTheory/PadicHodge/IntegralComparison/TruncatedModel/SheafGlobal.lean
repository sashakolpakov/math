import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobalData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionIntrinsicHomology

/-! # Sheaf Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobal.Comparison

noncomputable section

/-! The original global comparison in homology after the literal
sheaf-complex total comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mapped_comp {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c :=
  (F.map_comp a b).symm.trans (congrArg F.map h)

private theorem insert_factor {C : Type*} [Category C] {A B D E F : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : B ⟶ E} {e : E ⟶ F} {f : A ⟶ F}
    (h : b ≫ c = d) (hf : a ≫ d ≫ e = f) : a ≫ b ≫ c ≫ e = f := by
  rw [← Category.assoc b c e, h]
  exact hf

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

omit [Fintype k] [CharP k p] in
private theorem homology_composition
    {K L M : CochainComplex
      (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
    {a : K ⟶ L} {b : L ⟶ M} {d : K ⟶ M} (h : a ≫ b = d) (q : ℕ) :
    homologyMap a q ≫ homologyMap b q = homologyMap d q := by
  rw [← homologyMap_comp, h]

theorem homology_factor (q : ℕ) :
    homologyMap (SheafGlobalData.Comparison.totalUnit p k n X) q ≫ homologyMap (SheafGlobalData.Comparison.totalMap p k n X Y f hp I) q =
      homologyMap (OrdinaryGlobal.OrdinaryComparison.map p k n X Y f hp I) q :=
  homology_composition p k (SheafGlobalData.Comparison.comparison p k n X Y f hp I) q

private theorem homology_ordinary (q : ℕ) :
    homologyMap (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom q ≫
      homologyMap (OrdinaryGlobal.OrdinaryComparison.map p k n X Y f hp I) q ≫
      (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q).hom =
    (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom :=
  OrdinaryGlobal.OrdinaryComparison.homology_comparison p k n X Y f hp I q

omit [Fintype k] [CharP k p] in
private theorem homology_join
    {A B C D E : ModuleCat.{2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : B ⟶ D}
    {e : D ⟶ E} {f : A ⟶ E}
    (h : b ≫ c = d) (hf : a ≫ d ≫ e = f) : a ≫ b ≫ c ≫ e = f :=
  insert_factor h hf

theorem homology_comparison (q : ℕ) :
    homologyMap (OrdinaryGlobal.OrdinaryComparison.coordinates p k n X).hom q ≫
      homologyMap (SheafGlobalData.Comparison.totalUnit p k n X) q ≫
      homologyMap (SheafGlobalData.Comparison.totalMap p k n X Y f hp I) q ≫
      (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q).hom =
    (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom :=
  homology_join p k (homology_factor p k n X Y f hp I q)
    (homology_ordinary p k n X Y f hp I q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobal.Comparison
