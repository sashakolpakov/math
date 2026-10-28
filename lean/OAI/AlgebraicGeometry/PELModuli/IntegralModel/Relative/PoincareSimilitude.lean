import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PicardFunctions

/-! # Poincare Similitude -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareSimilitude.RelativePoincareClasses

noncomputable section

/-! The canonical polarization line on a varying family has the
actual fixed-power identity for every Rosati similitude over a reduced
noetherian base. The exponent depends only on the multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem pairClass_precomp {T U : Over S} (p : U ⟶ T)
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback p.left (PoincareEq.RelativePoincareClasses.pairClass D t a) = PoincareEq.RelativePoincareClasses.pairClass D (p ≫ t) (p ≫ a) := by
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp p.left (lift t a).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
    (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
      (congrArg Over.Hom.left (comp_lift p t a)))

theorem pairClass_adjoint (f : A.scheme ⟶ A.scheme)
    (q : D.abelian.scheme ⟶ D.abelian.scheme)
    (hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    {T : Over S} (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    PoincareEq.RelativePoincareClasses.pairClass D (t ≫ q) a = PoincareEq.RelativePoincareClasses.pairClass D t (a ≫ f) := by
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift t a).left) hq
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp] at h
  have hl : (lift t a).left ≫ (q ⊗ₘ 𝟙 A.scheme).left = (lift (t ≫ q) a).left := by
    simpa only [Category.comp_id, Over.comp_left] using congrArg Over.Hom.left (lift_map t a q (𝟙 A.scheme))
  have hr : (lift t a).left ≫ (𝟙 D.abelian.scheme ⊗ₘ f).left = (lift t (a ≫ f)).left := by
    simpa only [Category.comp_id, Over.comp_left] using congrArg Over.Hom.left (lift_map t a (𝟙 D.abelian.scheme) f)
  rw [hl, hr] at h
  exact h

def polarizationLine (ell : A.scheme ⟶ D.abelian.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (lift ell (𝟙 A.scheme)).left D.poincare

variable [IsReduced S] [IsNoetherian S]

local instance abelian_reduced : IsReduced A.scheme.left := by
  have : GeometricallyReduced A.scheme.hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth A.scheme.hom
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.scheme.hom

local instance abelian_noetherian : IsNoetherian A.scheme.left := by
  let : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  let : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  exact ⟨⟩

/-- The exponent depends only on the similitude multiplier, and the
identity concerns the fixed actual polarization line bundle. -/
theorem polarizationLine_pullback_class
    (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell]
    (f : A.scheme ⟶ A.scheme) (q : D.abelian.scheme ⟶ D.abelian.scheme)
    (hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    (n : ℕ) (h : f ≫ ell ≫ q = ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) ≫ ell) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationLine D ell)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationLine D ell) ^ n := by
  have hn : f ≫ ell ≫ q = ell ^ n := by
    rw [h, MonObj.pow_comp, Category.id_comp]
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f.left (PoincareEq.RelativePoincareClasses.pairClass D ell (𝟙 A.scheme)) =
    PoincareEq.RelativePoincareClasses.pairClass D ell (𝟙 A.scheme) ^ n
  rw [pairClass_precomp, Category.comp_id]
  have ha := pairClass_adjoint D f q hq (f ≫ ell) (𝟙 A.scheme)
  rw [Category.id_comp, Category.assoc, hn] at ha
  exact ha.symm.trans (PoincareEq.RelativePoincareClasses.pairClass_pow_left D ell (𝟙 A.scheme) n)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareSimilitude.RelativePoincareClasses
