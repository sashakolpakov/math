import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Point Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange.FamilyPointTransport

noncomputable section

section

/-! Transport of actual scheme points through isomorphisms of pulled-back
families, including its identity and composition laws. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} (A : Over S) (f g : T ⟶ S)

def liftPoint (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    T ⟶ ((Over.pullback f).obj A).left :=
  pullback.lift x (𝟙 T) (hx.trans (Category.id_comp f).symm)

@[reassoc (attr := simp)] theorem liftPoint_fst (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    liftPoint A f x hx ≫ pullback.fst A.hom f = x := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem liftPoint_snd (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    liftPoint A f x hx ≫ pullback.snd A.hom f = 𝟙 T := pullback.lift_snd _ _ _

def transport (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) : T ⟶ A.left :=
  liftPoint A f x hx ≫ e.hom.left ≫ pullback.fst A.hom g

@[reassoc] theorem transport_base
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) : transport A f g e x hx ≫ A.hom = g := by
  have he : e.hom.left ≫ pullback.snd A.hom g = pullback.snd A.hom f := e.hom.w
  simp only [transport, Category.assoc, pullback.condition, reassoc_of% he,
    liftPoint_snd_assoc]

theorem liftPoint_transport
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    liftPoint A g (transport A f g e x hx) (transport_base A f g e x hx) =
      liftPoint A f x hx ≫ e.hom.left := by
  apply pullback.hom_ext
  · exact (liftPoint_fst _ _ _ _).trans (Category.assoc _ _ _).symm
  · have he : e.hom.left ≫ pullback.snd A.hom g = pullback.snd A.hom f := e.hom.w
    simp only [liftPoint_snd, Category.assoc, he]

@[simp] theorem transport_refl (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    transport A f f (Iso.refl _) x hx = x := by
  simp only [transport, Iso.refl_hom, Over.id_left, Category.id_comp, liftPoint_fst]

theorem transport_trans {h : T ⟶ S}
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A)
    (d : (Over.pullback g).obj A ≅ (Over.pullback h).obj A)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    transport A g h d (transport A f g e x hx) (transport_base A f g e x hx) =
      transport A f h (e ≪≫ d) x hx := by
  change liftPoint A g (transport A f g e x hx) (transport_base A f g e x hx) ≫
    d.hom.left ≫ pullback.fst A.hom h =
      liftPoint A f x hx ≫ (e ≪≫ d).hom.left ≫ pullback.fst A.hom h
  rw [liftPoint_transport]
  simp only [Iso.trans_hom, Over.comp_left, Category.assoc]

end

/-! Transport of actual family points commutes with arbitrary pullback
through the canonical iterated-pullback comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T W : Scheme.{0}} (A : Over S) (f g : T ⟶ S) (k : W ⟶ T)

def nativeMap : ((Over.pullback (k ≫ f)).obj A).left ⟶ ((Over.pullback f).obj A).left :=
  ((Over.pullbackComp k f).hom.app A).left ≫ pullback.fst (pullback.snd A.hom f) k

@[reassoc] theorem nativeMap_fst :
    nativeMap A f k ≫ pullback.fst A.hom f = pullback.fst A.hom (k ≫ f) := by
  exact (Category.assoc _ _ _).trans (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst A f k)

@[reassoc] theorem nativeMap_snd :
    nativeMap A f k ≫ pullback.snd A.hom f = pullback.snd A.hom (k ≫ f) ≫ k := by
  have he : ((Over.pullbackComp k f).hom.app A).left ≫
      pullback.snd (pullback.snd A.hom f) k = pullback.snd A.hom (k ≫ f) :=
    ((Over.pullbackComp k f).hom.app A).w
  simp only [nativeMap, Category.assoc, pullback.condition, reassoc_of% he]

def baseChangeIso (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) :
    (Over.pullback (k ≫ f)).obj A ≅ (Over.pullback (k ≫ g)).obj A :=
  (Over.pullbackComp k f).app A ≪≫ (Over.pullback k).mapIso e ≪≫ ((Over.pullbackComp k g).app A).symm

theorem baseChangeIso_projection
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) :
    (baseChangeIso A f g k e).hom.left ≫ pullback.fst A.hom (k ≫ g) =
      nativeMap A f k ≫ e.hom.left ≫ pullback.fst A.hom g := by
  have hg : ((Over.pullbackComp k g).inv.app A).left ≫ pullback.fst A.hom (k ≫ g) =
      pullback.fst (pullback.snd A.hom g) k ≫ pullback.fst A.hom g := by
    exact (((Over.forget W).mapIso ((Over.pullbackComp k g).app A)).inv_comp_eq).mpr
      (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst A g k).symm
  change (((Over.pullbackComp k f).hom.app A).left ≫
    ((Over.pullback k).map e.hom).left ≫ ((Over.pullbackComp k g).inv.app A).left) ≫
      pullback.fst A.hom (k ≫ g) = _
  have hm : ((Over.pullback k).map e.hom).left ≫ pullback.fst (pullback.snd A.hom g) k =
      pullback.fst (pullback.snd A.hom f) k ≫ e.hom.left := pullback.lift_fst _ _ _
  simp only [Category.assoc, hg, reassoc_of% hm, nativeMap]

theorem liftPoint_nativeMap (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    liftPoint A (k ≫ f) (k ≫ x) (by rw [Category.assoc, hx]) ≫ nativeMap A f k =
      k ≫ liftPoint A f x hx := by
  apply pullback.hom_ext
  · rw [Category.assoc, nativeMap_fst, liftPoint_fst]
    simp only [Category.assoc, liftPoint_fst]
  · rw [Category.assoc, nativeMap_snd, ← Category.assoc, liftPoint_snd, Category.id_comp]
    simp only [Category.assoc, liftPoint_snd, Category.comp_id]

theorem transport_baseChange
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    transport A (k ≫ f) (k ≫ g) (baseChangeIso A f g k e)
      (k ≫ x) (by rw [Category.assoc, hx]) = k ≫ transport A f g e x hx := by
  change liftPoint A (k ≫ f) (k ≫ x) _ ≫
    (baseChangeIso A f g k e).hom.left ≫ pullback.fst A.hom (k ≫ g) = _
  rw [baseChangeIso_projection, ← Category.assoc _ (nativeMap A f k), liftPoint_nativeMap]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange.FamilyPointTransport
