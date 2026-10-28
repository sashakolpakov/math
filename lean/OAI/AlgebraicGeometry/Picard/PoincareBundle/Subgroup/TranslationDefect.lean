import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsomorphismDefectCocycle

/-! # Translation Defect -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect

noncomputable section

/-! The regular composition defect of actual subgroup transport is natural on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
open Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A]
  (i : H ⟶ A) (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

/-- Compare successive subgroup translations with a direct translation of the same line fibers. -/
def defect {T : Over S} (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z) : Γ(T.left, ⊤)ˣ :=
  Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L x) (TranslationFibers.transportIso i L t x y a hx ≪≫ TranslationFibers.transportIso i L t y z b hy)
    (TranslationFibers.transportIso i L t x z c hz)

theorem defect_eq_one_iff {T : Over S} (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z) :
    defect i L t x y z a b c hx hy hz = 1 ↔
      TranslationFibers.transportIso i L t x y a hx ≪≫ TranslationFibers.transportIso i L t y z b hy = TranslationFibers.transportIso i L t x z c hz :=
  Line.IsoRatios.ratio_eq_one_iff (FiberIsomorphismRatios.fiberLine L x) _ _

/-- The composition defect pulls back as an actual regular unit along every map of test schemes. -/
theorem defect_natural {T U : Over S} (g : U ⟶ T)
    (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z)
    (x' y' z' : U ⟶ A) (a' b' c' : U ⟶ H)
    (hx' : (a' ≫ i) * x' = y') (hy' : (b' ≫ i) * y' = z') (hz' : (c' ≫ i) * x' = z')
    (hxx : g ≫ x = x') (hyy : g ≫ y = y') (hzz : g ≫ z = z')
    (ha : g ≫ a = a') (hb : g ≫ b = b') (hc : g ≫ c = c') :
    defect i L t x' y' z' a' b' c' hx' hy' hz' =
      Units.map g.left.appTop.hom (defect i L t x y z a b c hx hy hz) := by
  apply FiberIsomorphismRatios.ratio_natural L
    (TranslationFibers.transportIso i L t x y a hx ≪≫ TranslationFibers.transportIso i L t y z b hy)
    (TranslationFibers.transportIso i L t x z c hz) g x' z' hxx hzz
  · exact (PullHom.pullHom_comp (F := Geometric.KernelLinearization.overModulePullbacks S) (L := L.sheaf) (M := L.sheaf) (N := L.sheaf)
      (x := x) (y := y) (z := z) (TranslationFibers.transportIso i L t x y a hx).hom
      (TranslationFibers.transportIso i L t y z b hy).hom g x' y' z' hxx hyy hzz).trans
        (congrArg₂ (fun m n => m ≫ n)
          (TranslationFibers.transport_natural i L t g x y a hx x' y' a' hx' hxx hyy ha)
          (TranslationFibers.transport_natural i L t g y z b hy y' z' b' hy' hyy hzz hb))
  · exact TranslationFibers.transport_natural i L t g x z c hz x' z' c' hz' hxx hzz hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect
