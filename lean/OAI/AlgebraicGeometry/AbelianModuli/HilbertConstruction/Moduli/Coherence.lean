import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Identity and composition laws for polarized full-level base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {δ : Fin g → ℕ} {S S' S'' : Scheme.{u}}

@[simp]
theorem Abelian.Schemes.AbelianScheme.pullbackIdIso_hom (A : Abelian.Schemes.AbelianScheme g S) :
    A.pullbackIdIso.hom = Over.pullbackId.hom.app A.scheme := by
  change Over.pullbackId.hom.app A.scheme ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The identity comparison is the projection from the identity base change. -/
theorem Moduli.Coherence.pullbackId_hom_left (X : Over S) :
    (Over.pullbackId.hom.app X).left = pullback.fst X.hom (𝟙 S) := by
  have w := conjugateEquiv_counit (Over.mapPullbackAdj (𝟙 S))
    (Adjunction.id (C := Over S)) (Over.mapId S).inv X
  have w' := congrArg (fun a => a.left) w
  change (Over.pullbackId.hom.app X).left ≫ 𝟙 _ =
    𝟙 _ ≫ pullback.fst X.hom (𝟙 S) at w'
  exact (Category.comp_id _).symm.trans (w'.trans (Category.id_comp _))

theorem Abelian.Schemes.AbelianScheme.pullbackIdIso_hom_left (A : Abelian.Schemes.AbelianScheme g S) :
    A.pullbackIdIso.hom.left = pullback.fst A.scheme.hom (𝟙 S) :=
  (congrArg (fun a : (A.pullback (𝟙 S)).scheme ⟶ A.scheme => a.left)
    A.pullbackIdIso_hom).trans (Moduli.Coherence.pullbackId_hom_left A.scheme)

/-- The identity comparison preserves the Poincare pullback map. -/
theorem Moduli.Coherence.poincarePullbackOverMap_id {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) :
    (D.abelian.pullbackIdIso.hom ⊗ₘ A.pullbackIdIso.hom).left =
      (D.poincarePullbackOverMap (𝟙 S)).left := by
  apply Over.tensorObj_ext
  · exact (Over.tensorHom_left_fst _ _ _ _).trans
      ((congrArg (fun z =>
        pullback.fst (D.abelian.pullback (𝟙 S)).scheme.hom (A.pullback (𝟙 S)).scheme.hom ≫ z)
        D.abelian.pullbackIdIso_hom_left).trans
          (D.poincarePullbackOverMap_left_fst (𝟙 S)).symm)
  · exact (Over.tensorHom_left_snd _ _ _ _).trans
      ((congrArg (fun z =>
        pullback.snd (D.abelian.pullback (𝟙 S)).scheme.hom (A.pullback (𝟙 S)).scheme.hom ≫ z)
        A.pullbackIdIso_hom_left).trans
          (D.poincarePullbackOverMap_left_snd (𝟙 S)).symm)

/-- The ordered basis is unchanged by the identity comparison of test schemes. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.basis_mapId_left {A : Abelian.Schemes.AbelianScheme g S}
    (level : A.FullLevel N) (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (level.hom.app (.op ((Over.map (𝟙 S)).obj T)) c).val.left =
      (level.hom.app (.op T) c).val.left := by
  have w := ConcreteCategory.congr_hom
    (level.hom.naturality ((Over.mapId S).inv.app T).op) c
  have w' := congrArg (fun x : A.torsionPoints N T => x.val.left) w
  change (level.hom.app (.op T) (c.comap ⟨𝟙 T.left, Scheme.Hom.continuous (𝟙 T.left)⟩)).val.left =
    𝟙 T.left ≫ (level.hom.app (.op ((Over.map (𝟙 S)).obj T)) c).val.left at w'
  have hc : c.comap ⟨𝟙 T.left, Scheme.Hom.continuous (𝟙 T.left)⟩ = c := by
    ext t
    rfl
  rw [hc, Category.id_comp] at w'
  exact w'.symm

/-- Identity base change preserves all the polarized full-level data. -/
def Moduli.Isomorphisms.LevelPreservingIso.pullbackId (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback (𝟙 S)) A where
  abelian := A.abelian.pullbackIdIso
  dual := A.dual.abelian.pullbackIdIso
  abelianGroup := A.abelian.pullbackIdIso_preservesGroup
  dualGroup := A.dual.abelian.pullbackIdIso_preservesGroup
  polarization := by
    change (Over.pullback (𝟙 S)).map A.polarization.isogeny.hom ≫
      A.dual.abelian.pullbackIdIso.hom =
        A.abelian.pullbackIdIso.hom ≫ A.polarization.isogeny.hom
    rw [Abelian.Schemes.AbelianScheme.pullbackIdIso_hom, Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality A.polarization.isogeny.hom
  poincare := congrArg (fun z => Line.Bundles.LineBundle.pullbackClass z
    (Line.Bundles.LineBundle.classOf A.dual.poincare)) (Moduli.Coherence.poincarePullbackOverMap_id A.dual)
  level T c := by
    apply Over.OverMorphism.ext
    exact (congrArg (fun z => ((A.level.pullback (𝟙 S)).hom.app (.op T) c).val.left ≫ z)
      A.abelian.pullbackIdIso_hom_left).trans
        ((congrArg (fun x : A.abelian.Points ((Over.map (𝟙 S)).obj T) => x.left)
          (A.level.pullback_basis (𝟙 S) T c)).trans (A.level.basis_mapId_left T c))

/-- Successive Poincare pullbacks agree under the composition comparison. -/
theorem Moduli.Coherence.poincarePullbackOverMap_comp {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    ((D.pullback f).poincarePullbackOverMap h).left ≫
        (D.poincarePullbackOverMap f).left =
      ((D.abelian.pullbackCompIso f h).inv ⊗ₘ (A.pullbackCompIso f h).inv).left ≫
        (D.poincarePullbackOverMap (h ≫ f)).left := by
  let A₁ := (A.pullback f).scheme
  let D₁ := (D.abelian.pullback f).scheme
  let A₂ := ((A.pullback f).pullback h).scheme
  let D₂ := ((D.abelian.pullback f).pullback h).scheme
  let A₃ := (A.pullback (h ≫ f)).scheme
  let D₃ := (D.abelian.pullback (h ≫ f)).scheme
  let q : (D₂ ⊗ A₂).left ⟶ (D₁ ⊗ A₁).left :=
    ((D.pullback f).poincarePullbackOverMap h).left
  let r : (D₁ ⊗ A₁).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    (D.poincarePullbackOverMap f).left
  let e : (D₂ ⊗ A₂).left ⟶ (D₃ ⊗ A₃).left :=
    ((D.abelian.pullbackCompIso f h).inv ⊗ₘ (A.pullbackCompIso f h).inv).left
  let t : (D₃ ⊗ A₃).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    (D.poincarePullbackOverMap (h ≫ f)).left
  change q ≫ r = e ≫ t
  apply Over.tensorObj_ext
  · have hq : q ≫ pullback.fst D₁.hom A₁.hom =
        pullback.fst D₂.hom A₂.hom ≫ pullback.fst D₁.hom h :=
      (D.pullback f).poincarePullbackOverMap_left_fst h
    have hr : r ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst D₁.hom A₁.hom ≫ pullback.fst D.abelian.scheme.hom f :=
      D.poincarePullbackOverMap_left_fst f
    have he : e ≫ pullback.fst D₃.hom A₃.hom =
        pullback.fst D₂.hom A₂.hom ≫ (D.abelian.pullbackCompIso f h).inv.left :=
      Over.tensorHom_left_fst _ _ _ _
    have ht : t ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst D₃.hom A₃.hom ≫ pullback.fst D.abelian.scheme.hom (h ≫ f) :=
      D.poincarePullbackOverMap_left_fst (h ≫ f)
    exact (Category.assoc q r _).trans
      ((congrArg (fun z => q ≫ z) hr).trans
        (((Category.assoc q _ _).symm.trans
          (congrArg (fun z => z ≫ pullback.fst D.abelian.scheme.hom f) hq)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => pullback.fst D₂.hom A₂.hom ≫ z)
              (D.abelian.pullbackCompIso_inv_left_fst f h).symm).trans
              (((Category.assoc _ _ _).symm.trans
                (congrArg (fun z => z ≫ pullback.fst D.abelian.scheme.hom (h ≫ f)) he.symm)).trans
                ((Category.assoc e _ _).trans
                  ((congrArg (fun z => e ≫ z) ht.symm).trans
                    (Category.assoc e t _).symm)))))))
  · have hq : q ≫ pullback.snd D₁.hom A₁.hom =
        pullback.snd D₂.hom A₂.hom ≫ pullback.fst A₁.hom h :=
      (D.pullback f).poincarePullbackOverMap_left_snd h
    have hr : r ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd D₁.hom A₁.hom ≫ pullback.fst A.scheme.hom f :=
      D.poincarePullbackOverMap_left_snd f
    have he : e ≫ pullback.snd D₃.hom A₃.hom =
        pullback.snd D₂.hom A₂.hom ≫ (A.pullbackCompIso f h).inv.left :=
      Over.tensorHom_left_snd _ _ _ _
    have ht : t ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd D₃.hom A₃.hom ≫ pullback.fst A.scheme.hom (h ≫ f) :=
      D.poincarePullbackOverMap_left_snd (h ≫ f)
    exact (Category.assoc q r _).trans
      ((congrArg (fun z => q ≫ z) hr).trans
        (((Category.assoc q _ _).symm.trans
          (congrArg (fun z => z ≫ pullback.fst A.scheme.hom f) hq)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => pullback.snd D₂.hom A₂.hom ≫ z)
              (A.pullbackCompIso_inv_left_fst f h).symm).trans
              (((Category.assoc _ _ _).symm.trans
                (congrArg (fun z => z ≫ pullback.fst A.scheme.hom (h ≫ f)) he.symm)).trans
                ((Category.assoc e _ _).trans
                  ((congrArg (fun z => e ≫ z) ht.symm).trans
                    (Category.assoc e t _).symm)))))))

/-- The ordered basis respects the canonical comparison of two maps of test schemes. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.basis_mapComp_left {A : Abelian.Schemes.AbelianScheme g S}
    (level : A.FullLevel N) (f : S' ⟶ S) (h : S'' ⟶ S') (T : Over S'')
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (level.hom.app (.op ((Over.map f).obj ((Over.map h).obj T))) c).val.left =
      (level.hom.app (.op ((Over.map (h ≫ f)).obj T)) c).val.left := by
  have w := ConcreteCategory.congr_hom
    (level.hom.naturality ((Over.mapComp h f).hom.app T).op) c
  have w' := congrArg
    (fun x : A.torsionPoints N ((Over.map (h ≫ f)).obj T) => x.val.left) w
  change (level.hom.app (.op ((Over.map (h ≫ f)).obj T))
      (c.comap ⟨𝟙 T.left, Scheme.Hom.continuous (𝟙 T.left)⟩)).val.left =
    𝟙 T.left ≫ (level.hom.app (.op ((Over.map f).obj ((Over.map h).obj T))) c).val.left at w'
  have hc : c.comap ⟨𝟙 T.left, Scheme.Hom.continuous (𝟙 T.left)⟩ = c := by
    ext t
    rfl
  rw [hc, Category.id_comp] at w'
  exact w'.symm

/-- Successive pullbacks give the same ordered basis under the abelian comparison. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.pullback_comp_basis {A : Abelian.Schemes.AbelianScheme g S}
    (level : A.FullLevel N) (f : S' ⟶ S) (h : S'' ⟶ S') (T : Over S'')
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (((level.pullback f).pullback h).hom.app (.op T) c).val ≫
        (A.pullbackCompIso f h).inv =
      ((level.pullback (h ≫ f)).hom.app (.op T) c).val := by
  apply (A.baseChangePointsEquiv (h ≫ f) T).injective
  apply Over.OverMorphism.ext
  let x := (((level.pullback f).pullback h).hom.app (.op T) c).val
  let y := ((level.pullback f).hom.app (.op ((Over.map h).obj T)) c).val
  let z := ((level.pullback (h ≫ f)).hom.app (.op T) c).val
  have hx : x.left ≫ pullback.fst (A.pullback f).scheme.hom h = y.left :=
    congrArg (fun a : (A.pullback f).Points ((Over.map h).obj T) => a.left)
      ((level.pullback f).pullback_basis h T c)
  have hy : y.left ≫ pullback.fst A.scheme.hom f =
      (level.hom.app (.op ((Over.map f).obj ((Over.map h).obj T))) c).val.left :=
    congrArg (fun a : A.Points ((Over.map f).obj ((Over.map h).obj T)) => a.left)
      (level.pullback_basis f ((Over.map h).obj T) c)
  have hz : z.left ≫ pullback.fst A.scheme.hom (h ≫ f) =
      (level.hom.app (.op ((Over.map (h ≫ f)).obj T)) c).val.left :=
    congrArg (fun a : A.Points ((Over.map (h ≫ f)).obj T) => a.left)
      (level.pullback_basis (h ≫ f) T c)
  change (x.left ≫ (A.pullbackCompIso f h).inv.left) ≫
    pullback.fst A.scheme.hom (h ≫ f) = z.left ≫ pullback.fst A.scheme.hom (h ≫ f)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => x.left ≫ a) (A.pullbackCompIso_inv_left_fst f h)).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ pullback.fst A.scheme.hom f) hx)).trans
        (hy.trans ((level.basis_mapComp_left f h T c).trans hz.symm))))

/-- Composition of base changes preserves the polarized full-level data. -/
def Moduli.Isomorphisms.LevelPreservingIso.pullbackComp (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    Moduli.Isomorphisms.LevelPreservingIso ((A.pullback f).pullback h) (A.pullback (h ≫ f)) where
  abelian := (A.abelian.pullbackCompIso f h).symm
  dual := (A.dual.abelian.pullbackCompIso f h).symm
  abelianGroup := inferInstanceAs (IsMonHom (A.abelian.pullbackCompIso f h).inv)
  dualGroup := inferInstanceAs (IsMonHom (A.dual.abelian.pullbackCompIso f h).inv)
  polarization := by
    change (Over.pullback h).map ((Over.pullback f).map A.polarization.isogeny.hom) ≫
      (A.dual.abelian.pullbackCompIso f h).inv =
        (A.abelian.pullbackCompIso f h).inv ≫
          (Over.pullback (h ≫ f)).map A.polarization.isogeny.hom
    rw [Abelian.Schemes.AbelianScheme.pullbackCompIso_inv, Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
    exact (Over.pullbackComp h f).inv.naturality A.polarization.isogeny.hom
  poincare :=
    (Line.Bundles.LineBundle.pullbackClass_comp
      ((A.dual.abelian.pullbackCompIso f h).inv ⊗ₘ (A.abelian.pullbackCompIso f h).inv).left
      (A.dual.poincarePullbackOverMap (h ≫ f)).left (Line.Bundles.LineBundle.classOf A.dual.poincare)).symm.trans
      ((congrArg (fun a => Line.Bundles.LineBundle.pullbackClass a (Line.Bundles.LineBundle.classOf A.dual.poincare))
        (Moduli.Coherence.poincarePullbackOverMap_comp A.dual f h).symm).trans
        (Line.Bundles.LineBundle.pullbackClass_comp ((A.dual.pullback f).poincarePullbackOverMap h).left
          (A.dual.poincarePullbackOverMap f).left (Line.Bundles.LineBundle.classOf A.dual.poincare)))
  level T c := A.level.pullback_comp_basis f h T c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
