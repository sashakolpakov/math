import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescentOnOver
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DescentReindex
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms

/-! # Over Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverDescent

noncomputable section

/-!
# An actual underlying recovery is a recovery over the original base
-/

open _root_.CategoryTheory Opposite

universe u v u' v'

variable {C : Type u} [Category.{v} C] {S : C} {A B : Over S} (f : A ⟶ B)
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  (D : (DescentReindexing.reindex (Over.forget S) F).DescentData (fun (_ : PUnit.{1}) => f))
  (P : F.obj (.mk (op B.left)))

/-- Compatibility on all underlying test objects gives compatibility on every test object over the base. -/
def liftHom
    (a : Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f.left) P ⟶
      UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D) :
    Pseudofunctor.DescentData.ofObj (F := DescentReindexing.reindex (Over.forget S) F)
      (f := fun (_ : PUnit.{1}) => f) P ⟶ D where
  hom i := a.hom i
  comm := by
    intro T q i j x y hx hy
    cases i
    cases j
    have h := a.comm q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
    rw [UnderlyingDescentOnOver.hom_eq f F D q x y hx hy] at h
    exact h.trans (congrArg (fun k => k ≫ (F.map y.left.op.toLoc).toFunctor.map (a.hom PUnit.unit))
      (Canonical.DescentReindex.ofObj_hom (Over.forget S) F f P q x y hx hy).symm)

/-- An actual isomorphism recovering the underlying datum recovers the full datum over the base. -/
def liftIso
    (e : Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f.left) P ≅
      UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D) :
    Pseudofunctor.DescentData.ofObj (F := DescentReindexing.reindex (Over.forget S) F)
      (f := fun (_ : PUnit.{1}) => f) P ≅ D := by
  have : IsIso ((liftHom f F D P e.hom).hom PUnit.unit) :=
    (DescentComponentIsomorphisms.componentIso F f.left e).isIso_hom
  exact DescentComponentIsomorphisms.isoOfComponent
    (DescentReindexing.reindex (Over.forget S) F) f (liftHom f F D P e.hom)

/-- The recovered isomorphism retains precisely the original recovery map on the cover. -/
theorem liftIso_hom
    (e : Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f.left) P ≅
      UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D) :
    (liftIso f F D P e).hom.hom PUnit.unit = e.hom.hom PUnit.unit := rfl

/-- Forgetting the base retains every actual isomorphism of descent data. -/
def underlyingIso
    {E : (DescentReindexing.reindex (Over.forget S) F).DescentData (fun (_ : PUnit.{1}) => f)}
    (e : D ≅ E) :
    UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D ≅
      UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) E :=
  Pseudofunctor.DescentData.isoMk
    (fun _ => DescentComponentIsomorphisms.componentIso
      (DescentReindexing.reindex (Over.forget S) F) f e) (by
    intro T q i j x y hx hy
    cases i
    cases j
    exact e.hom.comm (UnderlyingDescent.baseMap q) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q x hx)
      (UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q y hy)
      (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q x hx)
      (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q y hy))

/-- The canonical recovered object has the same canonical underlying descent datum. -/
def canonicalUnderlyingIso :
    Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f.left) P ≅
      UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f)
        (Pseudofunctor.DescentData.ofObj (F := DescentReindexing.reindex (Over.forget S) F)
          (f := fun (_ : PUnit.{1}) => f) P) :=
  Pseudofunctor.DescentData.isoMk (fun _ => Iso.refl _) (by
    intro T q i j x y hx hy
    cases i
    cases j
    change (F.map x.op.toLoc).toFunctor.map (𝟙 _) ≫ _ =
      _ ≫ (F.map y.op.toLoc).toFunctor.map (𝟙 _)
    erw [(F.map x.op.toLoc).toFunctor.map_id, (F.map y.op.toLoc).toFunctor.map_id,
      Category.id_comp, Category.comp_id]
    exact Canonical.DescentReindex.ofObj_hom (Over.forget S) F f P
      (UnderlyingDescent.baseMap q)
      (UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q x hx)
      (UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q y hy)
      (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q x hx)
      (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q y hy))

/-- A compatible recovery over the base gives the actual canonical recovery on all underlying test objects. -/
def lowerIso
    (e : Pseudofunctor.DescentData.ofObj (F := DescentReindexing.reindex (Over.forget S) F)
      (f := fun (_ : PUnit.{1}) => f) P ≅ D) :
    Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f.left) P ≅
      UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D :=
  canonicalUnderlyingIso f F P ≪≫ underlyingIso f F _ e

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OverDescent
