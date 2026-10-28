import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrames

/-! # Vertical Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalFrame.Construction

noncomputable section

/-! Normalize the actual abelian-zero-axis frame to the original
common zero frame. Over a field, proper-group rigidity makes this
normalization unique. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def poincareVerticalAxis : D.abelian.scheme ⟶ D.abelian.scheme ⊗ A.scheme :=
  lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ A.scheme)

instance poincareVerticalAxis_isMonHom : IsMonHom (poincareVerticalAxis D) := by
  unfold poincareVerticalAxis
  rw [Hom.one_def]
  infer_instance

theorem poincareVerticalAxis_origin : η[D.abelian.scheme] ≫ poincareVerticalAxis D = 1 := by
  rw [MonObj.one_eq_one]
  exact MonObj.one_comp _

def poincareVerticalFrameAtOrigin :
    (Scheme.Modules.pullback η[D.abelian.scheme].left).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule D.abelian.scheme.left) ≅
      (Scheme.Modules.pullback η[D.abelian.scheme].left).obj
        ((Scheme.Modules.pullback (poincareVerticalAxis D).left).obj D.poincare.sheaf) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso η[D.abelian.scheme].left ≪≫ OriginFrames.Construction.poincareZeroFrame D _ ≪≫
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison (poincareVerticalAxis D) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[D.abelian.scheme] 1
      (poincareVerticalAxis_origin D)).symm

theorem atPoint_eq_of_normalized {U E : Over S} (p : U ⟶ E)
    (P : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ (Scheme.Modules.pullback p.left).obj P.sheaf)
    {T : Over S} (t : T ⟶ U) (x : T ⟶ E) (ht : t ≫ p = x)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber P x)
    (he : (Scheme.Modules.pullback t.left).mapIso e =
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t.left ≪≫ z ≪≫ (Picard.PoincareBundle.GlobalPullbackFrame.comparison p P t x ht).symm) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint p P e t x ht = z := by
  unfold Picard.PoincareBundle.GlobalPullbackFrame.atPoint Picard.PoincareBundle.FrameRatioPullback.pullFrame
  rw [he]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]

variable {k : Type u} [Field k] {d : ℕ} {Ab : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} (Db : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData Ab)

theorem existsUnique_poincareVerticalAxisFrame :
    ∃! e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Db.abelian.scheme.left ≅
      (Scheme.Modules.pullback (poincareVerticalAxis Db).left).obj Db.poincare.sheaf,
      (Scheme.Modules.pullback η[Db.abelian.scheme].left).mapIso e = poincareVerticalFrameAtOrigin Db := by
  have : IsIso η[Db.abelian.scheme].left.appTop := ProductIsomorphisms.Construction.origin_appTop_isIso Db.abelian.scheme
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[Db.abelian.scheme].left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial Db.abelian.scheme.left) (Db.poincare.pullback (poincareVerticalAxis Db).left)
    (Classical.choice Db.normalizedAtAbelianZero).symm (poincareVerticalFrameAtOrigin Db)

def poincareVerticalAxisFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Db.abelian.scheme.left ≅
    (Scheme.Modules.pullback (poincareVerticalAxis Db).left).obj Db.poincare.sheaf :=
  Classical.choose (existsUnique_poincareVerticalAxisFrame Db)

theorem poincareVerticalAxisFrame_origin :
    (Scheme.Modules.pullback η[Db.abelian.scheme].left).mapIso (poincareVerticalAxisFrame Db) =
      poincareVerticalFrameAtOrigin Db :=
  (Classical.choose_spec (existsUnique_poincareVerticalAxisFrame Db)).1

theorem poincareVerticalAxisFrame_at_origin :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (poincareVerticalAxis Db) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) (poincareVerticalAxisFrame Db)
      η[Db.abelian.scheme] 1 (poincareVerticalAxis_origin Db) = OriginFrames.Construction.poincareZeroFrame Db _ := by
  exact atPoint_eq_of_normalized (poincareVerticalAxis Db) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db)
    (poincareVerticalAxisFrame Db) η[Db.abelian.scheme] 1 (poincareVerticalAxis_origin Db)
    (OriginFrames.Construction.poincareZeroFrame Db _) (poincareVerticalAxisFrame_origin Db)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalFrame.Construction
