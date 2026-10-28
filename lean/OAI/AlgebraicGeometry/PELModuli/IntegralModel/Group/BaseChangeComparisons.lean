import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ParameterDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Base Change Comparisons -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange

noncomputable section

section

/-! Group-scheme coherence for arbitrary iterated base change, including
the exact finite-extension/complex-embedding comparison used in IntegralModel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' S'' : Scheme} (H : Over S) [GrpObj H]

def compositeMonIso (f : S' ⟶ S) (h : S'' ⟶ S') :
    Mon.mk ((Over.pullback (h ≫ f)).obj H) ≅
      Mon.mk ((Over.pullback h).obj ((Over.pullback f).obj H)) :=
  (Functor.mapMonNatIso (Over.pullbackComp h f)).app (Mon.mk H) ≪≫
    (Functor.mapMonCompIso (F := Over.pullback f) (G := Over.pullback h)).app (Mon.mk H)

def compositeIso (f : S' ⟶ S) (h : S'' ⟶ S') :
    (Over.pullback (h ≫ f)).obj H ≅ (Over.pullback h).obj ((Over.pullback f).obj H) :=
  (Over.pullbackComp h f).app H

theorem compositeMonIso_hom (f : S' ⟶ S) (h : S'' ⟶ S') :
    (compositeMonIso H f h).hom.hom = (compositeIso H f h).hom := by
  change (Over.pullbackComp h f).hom.app H ≫ 𝟙 _ = _
  exact Category.comp_id _

instance compositeIso_isMonHom (f : S' ⟶ S) (h : S'' ⟶ S') :
    IsMonHom (compositeIso H f h).hom := by
  rw [← compositeMonIso_hom H f h]
  exact inferInstanceAs (IsMonHom (compositeMonIso H f h).hom.hom)

instance compositeIso_inv_isMonHom (f : S' ⟶ S) (h : S'' ⟶ S') :
    IsMonHom (compositeIso H f h).inv := by infer_instance

omit [GrpObj H] in
theorem compositeIso_hom (f : S' ⟶ S) (h : S'' ⟶ S') :
    (compositeIso H f h).hom = (Over.pullbackComp h f).hom.app H := rfl

omit [GrpObj H] in
theorem compositeIso_inv_fst (f : S' ⟶ S) (h : S'' ⟶ S') :
    (compositeIso H f h).inv.left ≫ pullback.fst H.hom (h ≫ f) =
      pullback.fst (pullback.snd H.hom f) h ≫ pullback.fst H.hom f := by
  let e := (Over.forget S'').mapIso (compositeIso H f h)
  apply e.inv_comp_eq.mpr
  have he : e.hom = ((Over.pullbackComp h f).hom.app H).left :=
    congrArg Over.Hom.left (compositeIso_hom H f h)
  exact ((congrArg (fun a => a ≫ pullback.fst (pullback.snd H.hom f) h ≫
    pullback.fst H.hom f) he).trans (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst H f h)).symm

def congrMap (f g : S' ⟶ S) (w : f = g) : (Over.pullback f).obj H ⟶ (Over.pullback g).obj H :=
  Over.homMk (pullback.lift (pullback.fst H.hom f) (pullback.snd H.hom f)
    ((pullback.condition).trans (congrArg (fun a => pullback.snd H.hom f ≫ a) w)))
    (pullback.lift_snd _ _ _)

omit [GrpObj H] in
theorem congrMap_self (f : S' ⟶ S) : congrMap H f f rfl = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm
  · exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm

omit [GrpObj H] in
theorem congrMap_inverse (f g : S' ⟶ S) (w : f = g) :
    congrMap H f g w ≫ congrMap H g f w.symm = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp only [Over.comp_left, congrMap, Over.homMk_left, Category.assoc,
      pullback.lift_fst, pullback.lift_snd, Over.id_left, Category.id_comp]

def congrIso (f g : S' ⟶ S) (w : f = g) : (Over.pullback f).obj H ≅ (Over.pullback g).obj H :=
  ⟨congrMap H f g w, congrMap H g f w.symm,
    congrMap_inverse H f g w, congrMap_inverse H g f w.symm⟩

instance congrIso_isMonHom (f g : S' ⟶ S) (w : f = g) : IsMonHom (congrIso H f g w).hom := by
  cases w
  change IsMonHom (congrMap H f f rfl)
  rw [congrMap_self H f]
  infer_instance

omit [GrpObj H] in
theorem congrIso_fst (f g : S' ⟶ S) (w : f = g) :
    (congrIso H f g w).hom.left ≫ pullback.fst H.hom g = pullback.fst H.hom f :=
  pullback.lift_fst _ _ _

def iteratedIso (f : S' ⟶ S) (h : S'' ⟶ S') (g : S'' ⟶ S) (w : h ≫ f = g) :
    (Over.pullback h).obj ((Over.pullback f).obj H) ≅ (Over.pullback g).obj H :=
  (compositeIso H f h).symm ≪≫ congrIso H (h ≫ f) g w

instance iteratedIso_isMonHom (f : S' ⟶ S) (h : S'' ⟶ S') (g : S'' ⟶ S) (w : h ≫ f = g) :
    IsMonHom (iteratedIso H f h g w).hom := by
  change IsMonHom ((compositeIso H f h).inv ≫ (congrIso H (h ≫ f) g w).hom)
  infer_instance

omit [GrpObj H] in
theorem iteratedIso_fst (f : S' ⟶ S) (h : S'' ⟶ S') (g : S'' ⟶ S) (w : h ≫ f = g) :
    (iteratedIso H f h g w).hom.left ≫ pullback.fst H.hom g =
      pullback.fst (pullback.snd H.hom f) h ≫ pullback.fst H.hom f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun a => (compositeIso H f h).inv.left ≫ a) (congrIso_fst H _ _ w)).trans
      (compositeIso_inv_fst H f h))

omit [GrpObj H] in
theorem iteratedIso_hom_inv_id (f : S' ⟶ S) (h : S'' ⟶ S') (g : S'' ⟶ S) (w : h ≫ f = g) :
    (iteratedIso H f h g w).hom ≫ (iteratedIso H f h g w).inv = 𝟙 _ :=
  (iteratedIso H f h g w).hom_inv_id

omit [GrpObj H] in
theorem iteratedIso_inv_hom_id (f : S' ⟶ S) (h : S'' ⟶ S') (g : S'' ⟶ S) (w : h ≫ f = g) :
    (iteratedIso H f h g w).inv ≫ (iteratedIso H f h g w).hom = 𝟙 _ :=
  (iteratedIso H f h g w).inv_hom_id

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

theorem arithmeticComplexBaseEq (B : Base.ArithmeticBaseExtension K κ) :
    Spec.map (CommRingCat.ofHom B.embedding) ≫ B.fieldExtension = Spec.map (CommRingCat.ofHom κ) :=
  B.complexFieldMap.w

def arithmeticComplexIso (B : Base.ArithmeticBaseExtension K κ) (H : Over (Spec (.of K))) :
    (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj
        ((Over.pullback B.fieldExtension).obj H) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj H :=
  iteratedIso H B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (arithmeticComplexBaseEq B)

instance arithmeticComplexIso_isMonHom (B : Base.ArithmeticBaseExtension K κ)
    (H : Over (Spec (.of K))) [GrpObj H] : IsMonHom (arithmeticComplexIso B H).hom :=
  iteratedIso_isMonHom H B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (arithmeticComplexBaseEq B)

theorem arithmeticComplexIso_fst (B : Base.ArithmeticBaseExtension K κ)
    (H : Over (Spec (.of K))) :
    (arithmeticComplexIso B H).hom.left ≫ pullback.fst H.hom (Spec.map (CommRingCat.ofHom κ)) =
      pullback.fst (pullback.snd H.hom B.fieldExtension) (Spec.map (CommRingCat.ofHom B.embedding)) ≫
        pullback.fst H.hom B.fieldExtension :=
  iteratedIso_fst H B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (arithmeticComplexBaseEq B)

theorem arithmeticComplexIso_hom_inv_id (B : Base.ArithmeticBaseExtension K κ)
    (H : Over (Spec (.of K))) :
    (arithmeticComplexIso B H).hom ≫ (arithmeticComplexIso B H).inv = 𝟙 _ :=
  iteratedIso_hom_inv_id H B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (arithmeticComplexBaseEq B)

theorem arithmeticComplexIso_inv_hom_id (B : Base.ArithmeticBaseExtension K κ)
    (H : Over (Spec (.of K))) :
    (arithmeticComplexIso B H).inv ≫ (arithmeticComplexIso B H).hom = 𝟙 _ :=
  iteratedIso_inv_hom_id H B.fieldExtension (Spec.map (CommRingCat.ofHom B.embedding))
    (Spec.map (CommRingCat.ofHom κ)) (arithmeticComplexBaseEq B)

end

/-! Natural versions of the explicit pullback comparisons. Their components
are the native pullback maps, avoiding transports through chosen limits. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T U : Scheme}

def congrNatIso (f g : T ⟶ S) (w : f = g) : Over.pullback f ≅ Over.pullback g :=
  NatIso.ofComponents (fun X => congrIso X f g w) (by
    intro X Y a
    cases w
    change (Over.pullback f).map a ≫ congrMap Y f f rfl =
      congrMap X f f rfl ≫ (Over.pullback f).map a
    rw [congrMap_self, congrMap_self, Category.comp_id, Category.id_comp])

def iteratedNatIso (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g) :
    Over.pullback f ⋙ Over.pullback h ≅ Over.pullback g :=
  (Over.pullbackComp h f).symm ≪≫ congrNatIso (h ≫ f) g w

theorem iteratedNatIso_hom_app (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S)
    (w : h ≫ f = g) (X : Over S) :
    ((iteratedNatIso f h g w).app X).hom = (iteratedIso X f h g w).hom := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange
