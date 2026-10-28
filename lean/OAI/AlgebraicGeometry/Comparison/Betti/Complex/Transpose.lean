import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Transpose -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.Transpose

noncomputable section

/-! Transposition and extension of the actual functors of section complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ZeroObject

variable {T : Type*} [Category* T] {C : Type*} [Category* C]
  [Preadditive C] [HasZeroObject C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

def transpose (F : T ⥤ HomologicalComplex C c) : HomologicalComplex (T ⥤ C) c where
  X i := F ⋙ HomologicalComplex.eval _ _ i
  d i j :=
    { app := fun t => (F.obj t).d i j
      naturality := fun _ _ f => (F.map f).comm i j }
  shape i j h := NatTrans.ext (funext (fun t => (F.obj t).shape i j h))
  d_comp_d' i j k _ _ := NatTrans.ext (funext (fun t => (F.obj t).d_comp_d i j k))

def transposeMap {F G : T ⥤ HomologicalComplex C c} (φ : F ⟶ G) : transpose F ⟶ transpose G where
  f i :=
    { app := fun t => (φ.app t).f i
      naturality := fun _ _ f => congrArg (fun k => k.f i) (φ.naturality f) }
  comm' i j _ := NatTrans.ext (funext (fun t => (φ.app t).comm i j))

def optionXIso (F : T ⥤ HomologicalComplex C c) (i : Option ι) (t : T) :
    HomologicalComplex.extend.X (F.obj t) i ≅
      (HomologicalComplex.extend.X (transpose F) i).obj t :=
  match i with
  | some _ => Iso.refl _
  | none => (((evaluation T C).obj t).mapZeroObject).symm

theorem optionXIso_naturality (F : T ⥤ HomologicalComplex C c)
    (i : Option ι) {t s : T} (f : t ⟶ s) :
    HomologicalComplex.extend.mapX (F.map f) i ≫ (optionXIso F i s).hom =
      (optionXIso F i t).hom ≫ (HomologicalComplex.extend.X (transpose F) i).map f := by
  cases i with
  | none => exact (isZero_zero C).eq_of_src _ _
  | some i =>
    change (F.map f).f i ≫ 𝟙 ((F.obj s).X i) = 𝟙 ((F.obj t).X i) ≫ (F.map f).f i
    simp only [Category.comp_id, Category.id_comp]

def transposeExtendXIso (F : T ⥤ HomologicalComplex C c) (e : c.Embedding c') (i : ι') :
    (transpose (F ⋙ e.extendFunctor C)).X i ≅ ((transpose F).extend e).X i :=
  NatIso.ofComponents (fun t => optionXIso F (e.r i) t)
    (fun f => optionXIso_naturality F (e.r i) f)

theorem optionXIso_d (F : T ⥤ HomologicalComplex C c) (i j : Option ι) (t : T) :
    (optionXIso F i t).hom ≫ (HomologicalComplex.extend.d (transpose F) i j).app t =
      HomologicalComplex.extend.d (F.obj t) i j ≫ (optionXIso F j t).hom := by
  cases i with
  | none => exact (isZero_zero C).eq_of_src _ _
  | some i =>
    cases j with
    | none => exact (((evaluation T C).obj t).map_isZero (isZero_zero (T ⥤ C))).eq_of_tgt _ _
    | some j =>
      change 𝟙 ((F.obj t).X i) ≫ (F.obj t).d i j = (F.obj t).d i j ≫ 𝟙 ((F.obj t).X j)
      simp only [Category.comp_id, Category.id_comp]

/-- Extension and transposition give canonically isomorphic complexes of functors. -/
def transposeExtendIso (F : T ⥤ HomologicalComplex C c) (e : c.Embedding c') :
    transpose (F ⋙ e.extendFunctor C) ≅ (transpose F).extend e :=
  HomologicalComplex.Hom.isoOfComponents (transposeExtendXIso F e) (by
    intro i j _
    apply NatTrans.ext
    funext t
    exact optionXIso_d F (e.r i) (e.r j) t)

theorem optionXIso_map {F G : T ⥤ HomologicalComplex C c} (φ : F ⟶ G) (i : Option ι) (t : T) :
    HomologicalComplex.extend.mapX (φ.app t) i ≫ (optionXIso G i t).hom =
      (optionXIso F i t).hom ≫ (HomologicalComplex.extend.mapX (transposeMap φ) i).app t := by
  cases i with
  | none => exact (isZero_zero C).eq_of_src _ _
  | some i =>
    change (φ.app t).f i ≫ 𝟙 ((G.obj t).X i) = 𝟙 ((F.obj t).X i) ≫ (φ.app t).f i
    simp only [Category.comp_id, Category.id_comp]

theorem transposeExtendIso_naturality (e : c.Embedding c')
    {F G : T ⥤ HomologicalComplex C c} (φ : F ⟶ G) :
    transposeMap (Functor.whiskerRight φ (e.extendFunctor C)) ≫ (transposeExtendIso G e).hom =
      (transposeExtendIso F e).hom ≫ HomologicalComplex.extendMap (transposeMap φ) e := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext t
  exact optionXIso_map φ (e.r i) t

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.Transpose
