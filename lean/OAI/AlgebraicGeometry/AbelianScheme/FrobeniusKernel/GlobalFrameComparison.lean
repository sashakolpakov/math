import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

/-! # Global Frame Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GlobalFrameComparison.Construction

noncomputable section

/-! Canonical comparisons of two line fibers framed by the same global
zero trivialization commute with arbitrary parameter base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w v'

theorem framedIsoComparison_natural {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{v'} D] (F : C ⥤ D)
    {O A B : C} {O' A' B' : D}
    (eA : O ≅ A) (eB : O ≅ B) (u : O' ≅ F.obj O)
    (cA : F.obj A ≅ A') (cB : F.obj B ≅ B') (eA' : O' ≅ A') (eB' : O' ≅ B')
    (hA : u ≪≫ F.mapIso eA ≪≫ cA = eA') (hB : u ≪≫ F.mapIso eB ≪≫ cB = eB') :
    F.mapIso (eA.symm ≪≫ eB) ≪≫ cB = cA ≪≫ eA'.symm ≪≫ eB' := by
  subst eA'
  subst eB'
  apply Iso.ext
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E) (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
variable (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ (Scheme.Modules.pullback p.left).obj L.sheaf)

def globallyFramedFiberIso {T : Over S} (a b : T ⟶ K) (x y : T ⟶ E)
    (ha : a ≫ p = x) (hb : b ≫ p = y) : Picard.PoincareBundle.Line.Fibers.fiber L x ≅ Picard.PoincareBundle.Line.Fibers.fiber L y :=
  (Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s a x ha).symm ≪≫ Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s b y hb

theorem globallyFramedFiberIso_pullback {T U : Over S} (t : U ⟶ T)
    (a b : T ⟶ K) (x y : T ⟶ E) (ha : a ≫ p = x) (hb : b ≫ p = y)
    (a' b' : U ⟶ K) (x' y' : U ⟶ E) (ha' : a' ≫ p = x') (hb' : b' ≫ p = y')
    (hta : t ≫ a = a') (htb : t ≫ b = b') (htx : t ≫ x = x') (hty : t ≫ y = y') :
    (Scheme.Modules.pullback t.left).mapIso (globallyFramedFiberIso p L s a b x y ha hb) ≪≫
        Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t y y' hty =
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t x x' htx ≪≫ globallyFramedFiberIso p L s a' b' x' y' ha' hb' := by
  exact framedIsoComparison_natural (Scheme.Modules.pullback t.left)
    (Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s a x ha) (Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s b y hb) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t.left).symm
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t x x' htx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t y y' hty)
    (Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s a' x' ha') (Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s b' y' hb')
    (Picard.PoincareBundle.GlobalFrameNaturality.atPoint_pullback p L s t a x ha a' x' ha' hta htx)
    (Picard.PoincareBundle.GlobalFrameNaturality.atPoint_pullback p L s t b y hb b' y' hb' htb hty)

theorem globallyFramedFiberIso_pullHom {T U : Over S} (t : U ⟶ T)
    (a b : T ⟶ K) (x y : T ⟶ E) (ha : a ≫ p = x) (hb : b ≫ p = y)
    (a' b' : U ⟶ K) (x' y' : U ⟶ E) (ha' : a' ≫ p = x') (hb' : b' ≫ p = y')
    (hta : t ≫ a = a') (htb : t ≫ b = b') (htx : t ≫ x = x') (hty : t ≫ y = y') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S)
        (globallyFramedFiberIso p L s a b x y ha hb).hom t x' y' htx hty =
      (globallyFramedFiberIso p L s a' b' x' y' ha' hb').hom := by
  have hn := congrArg Iso.hom
    (globallyFramedFiberIso_pullback p L s t a b x y ha hb a' b' x' y' ha' hb' hta htb htx hty)
  change (Scheme.Modules.pullback t.left).map (globallyFramedFiberIso p L s a b x y ha hb).hom ≫
      (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t y y' hty).hom =
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t x x' htx).hom ≫ (globallyFramedFiberIso p L s a' b' x' y' ha' hb').hom at hn
  exact (Picard.PoincareBundle.Line.Fibers.pullHom_eq L
    (globallyFramedFiberIso p L s a b x y ha hb).hom t x' y' htx hty).trans
      ((congrArg (fun m => (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t x x' htx).inv ≫ m) hn).trans
        (Iso.inv_hom_id_assoc (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L t x x' htx) _))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GlobalFrameComparison.Construction
