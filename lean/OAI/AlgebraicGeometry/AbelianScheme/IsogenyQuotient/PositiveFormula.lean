import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Positive Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula.Construction

noncomputable section

/-!
Transport the normalized ample Poincare formula along actual group-scheme
isomorphisms. This will identify a field polarization's positivity with
the positivity clause for the corresponding relative geometric fiber.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-- The normalized ample formula, expressed on the field group itself. -/
def PositivePoincareFormula
    {K : Type u} [Field K] (B : Over (Spec (.of K))) [GrpObj B]
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left) : Prop :=
  ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left,
    L.IsAmple ∧
    Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback η[B].left L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K))) ∧
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (fst B B).left L).sheaf)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (snd B B).left L).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback μ[B].left L).sheaf)

private def formulaPullbackSquareIso
    {W X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback b L)).sheaf ≅
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback d L)).sheaf :=
  (Scheme.Modules.pullbackComp a b).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp c d).symm.app L.sheaf

/-- Pull back the formula, including the ample bundle and both sheaf
isomorphisms, along a group-scheme isomorphism. -/
theorem positivePoincareFormula_of_iso
    {K : Type u} [Field K] {B C : Over (Spec (.of K))} [GrpObj B] [GrpObj C]
    (e : B ≅ C) [IsMonHom e.hom]
    (QB : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left) (QC : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (C ⊗ C).left)
    (eQ : QB.sheaf ≅ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (e.hom ⊗ₘ e.hom).left QC).sheaf)
    (hp : PositivePoincareFormula C QC) : PositivePoincareFormula B QB := by
  obtain ⟨L, hL, ⟨eZero⟩, ⟨eFormula⟩⟩ := hp
  let e₂ := (Over.forget (Spec (.of K))).mapIso (e ⊗ᵢ e)
  let L' := L.pullback e.hom.left
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map e.hom))
  have hone : η[B].left ≫ e.hom.left = η[C].left :=
    congrArg (fun a => a.left) (IsMonHom.one_hom e.hom)
  have hmul : e₂.hom ≫ μ[C].left = μ[B].left ≫ e.hom.left :=
    (congrArg (fun a => a.left) (IsMonHom.mul_hom e.hom)).symm
  refine ⟨L', hL.pullback_of_isIso e.hom.left, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp η[B].left e.hom.left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hone).app L.sheaf ≪≫ eZero
  · let Q₁ := (L.pullback (fst C C).left).sheaf
    let Q₂ := (L.pullback (snd C C).left).sheaf
    let e₁ : (L'.pullback (fst B B).left).sheaf ≅
        (Scheme.Modules.pullback e₂.hom).obj Q₁ :=
      formulaPullbackSquareIso (fst B B).left e.hom.left e₂.hom (fst C C).left
        (Over.tensorHom_left_fst _ _ _ _).symm L
    let e₃ : (L'.pullback (snd B B).left).sheaf ≅
        (Scheme.Modules.pullback e₂.hom).obj Q₂ :=
      formulaPullbackSquareIso (snd B B).left e.hom.left e₂.hom (snd C C).left
        (Over.tensorHom_left_snd _ _ _ _).symm L
    exact AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr eQ e₁ ≪≫ (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModulePullbackIso e₂.hom QC.sheaf Q₁).symm) e₃ ≪≫
      (AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange.tensorModulePullbackIso e₂.hom (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule QC.sheaf Q₁) Q₂).symm ≪≫
      (Scheme.Modules.pullback e₂.hom).mapIso eFormula ≪≫
      formulaPullbackSquareIso e₂.hom μ[C].left μ[B].left e.hom.left hmul L

/-- Positivity is invariant under this concrete Poincare comparison. -/
theorem positivePoincareFormula_iff_of_iso
    {K : Type u} [Field K] {B C : Over (Spec (.of K))} [GrpObj B] [GrpObj C]
    (e : B ≅ C) [IsMonHom e.hom]
    (QB : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left) (QC : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (C ⊗ C).left)
    (eQ : QB.sheaf ≅ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (e.hom ⊗ₘ e.hom).left QC).sheaf) :
    PositivePoincareFormula B QB ↔ PositivePoincareFormula C QC := by
  refine ⟨?_, positivePoincareFormula_of_iso e QB QC eQ⟩
  intro h
  let e₂ := (Over.forget (Spec (.of K))).mapIso (e ⊗ᵢ e)
  let q : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback e₂.inv QB).sheaf ≅ QC.sheaf :=
    (Scheme.Modules.pullback e₂.inv).mapIso eQ ≪≫
      (Scheme.Modules.pullbackComp e₂.inv e₂.hom).app QC.sheaf ≪≫
      (Scheme.Modules.pullbackCongr e₂.inv_hom_id).app QC.sheaf ≪≫
      (Scheme.Modules.pullbackId _).app QC.sheaf
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact positivePoincareFormula_of_iso e.symm QC QB q.symm h

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic field formula on an iterated fiber is equivalent to
the relative formula on the fiber of the composite base map. -/
theorem positiveOnGeometricFiber_pullback_iff
    {S S' : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : S' ⟶ S) (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S') :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber (D.pullback f) ((Over.pullback f).map p) K s ↔
      AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K (s ≫ f) := by
  let e := (A.pullbackCompIso f s).symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom (A.pullbackCompIso f s).inv)
  exact positivePoincareFormula_iff_of_iso e
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt (D.pullback f) ((Over.pullback f).map p) s)
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p (s ≫ f))
    (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionCompIso D p f s)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula.Construction
