import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PureRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.PushforwardRelativeAdditiveCech

/-! # Pure Pushforward Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PurePushforwardRefinement

noncomputable section

/-! Relative refinement is invertible for a pure complex whose survivor
is an actual pushforward. Coverage is required only on that source. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
private theorem square_isIso {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : D ⟶ E) (e : A ⟶ D) (f : B ⟶ E)
    [IsIso b] [IsIso e] [IsIso f] (h : e ≫ b = a ≫ f) : IsIso a := by
  have ha : a = e ≫ b ≫ inv f := by
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
      (congrArg (· ≫ inv f) h).symm
  rw [ha]
  infer_instance

variable {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
  (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → Y.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → Y.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)
  (O : X.Opens)
  (hVO : iSup (fun i => f ⁻¹ᵁ (U ⊓ V i)) = O)
  (hWO : iSup (fun i => f ⁻¹ᵁ (U ⊓ W i)) = O)
  (haV : ∀ i, IsAffineOpen (f ⁻¹ᵁ (U ⊓ V i)))
  (haW : ∀ i, IsAffineOpen (f ⁻¹ᵁ (U ⊓ W i)))
  (K : CochainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (M : X.Modules) [hM : M.IsQuasicoherent]
  (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj M)

def survivorIso :
    AdditiveCechConcentration.coefficients ((single Y.Modules (.up ℕ) c).obj (K.homology c)) ≅
      PushforwardRelativeAdditiveCech.coefficientComplex f ((single X.Modules (.up ℕ) c).obj M) :=
  ((Scheme.Modules.toPresheaf Y).mapHomologicalComplex (.up ℕ)).mapIso
    ((single Y.Modules (.up ℕ) c).mapIso e ≪≫
      ((singleMapHomologicalComplex (Scheme.Modules.pushforward f) (.up ℕ) c).app M).symm)

include O hVO hWO haV haW M hM e in
omit [Y.IsSeparated] [∀ (q : ℕ), (K.X q).IsQuasicoherent] in
theorem survivor_isIso (q : ℕ) : IsIso (RelativeCech.Refinement.homology U V W r
    (AdditiveCechConcentration.coefficients ((single Y.Modules (.up ℕ) c).obj (K.homology c))) q) := by
  let : ∀ k, (((single X.Modules (.up ℕ) c).obj M).X k).IsQuasicoherent :=
    QuasicoherentTruncation.single M c
  let := PushforwardRelativeAdditiveCech.homology_isIso f U V W r O hVO hWO haV haW
    ((single X.Modules (.up ℕ) c).obj M) q
  let z := survivorIso f K c M e
  let α := homologyMap (RelativeCech.Total.sourceMap U V z.hom) q
  let β := homologyMap (RelativeCech.Total.sourceMap U W z.hom) q
  let : IsIso α := by
    change IsIso (((RelativeCech.Total.localFunctor U V).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ) ⋙
        homologyFunctor AddCommGrpCat.{u} (.up ℕ) q).map z.hom)
    infer_instance
  let : IsIso β := by
    change IsIso (((RelativeCech.Total.localFunctor U W).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ) ⋙
        homologyFunctor AddCommGrpCat.{u} (.up ℕ) q).map z.hom)
    infer_instance
  exact square_isIso _ _ α β (RelativeCech.Refinement.homology_naturality U V W r z.hom q)

include hU hV hW hK O hVO hWO haV haW M hM e in
theorem isIso (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients K) q) := by
  let := survivor_isIso f U V W r O hVO hWO haV haW K c M e q
  exact PureRefinement.isIso U hU V hV W hW r K c hK q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PurePushforwardRefinement
