import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Fiber Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Comparison of the Poincare formula on iterated geometric fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S S' S'' : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

/-- The actual scheme map used to define the polarization biextension on a fiber. -/
def Polarization.FiberComparison.polarizationBiextensionMap (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : S' ⟶ S) : ((A.pullback f).scheme ⊗ (A.pullback f).scheme).left ⟶
      (D.abelian.scheme ⊗ A.scheme).left :=
  ((Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme).left ≫ PolarizationData.poincareBaseChangeMap D f

@[reassoc (attr := simp)]
theorem Polarization.FiberComparison.polarizationBiextensionMap_fst (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : S' ⟶ S) :
    Polarization.FiberComparison.polarizationBiextensionMap D p f ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
      pullback.fst (A.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        pullback.fst A.scheme.hom f ≫ p.left := by
  let t := (Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme
  have ht : t.left ≫ pullback.fst (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom =
      pullback.fst (A.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        ((Over.pullback f).map p).left := Over.tensorHom_left_fst _ _ _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => t.left ≫ a) (Pullback.Comparisons.poincareBaseChangeMap_fst D f)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ pullback.fst D.abelian.scheme.hom f) ht).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun a => pullback.fst (A.pullback f).scheme.hom
              (A.pullback f).scheme.hom ≫ a) (Pullback.Comparisons.overPullback_map_left_fst p f))))))

@[reassoc (attr := simp)]
theorem Polarization.FiberComparison.polarizationBiextensionMap_snd (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : S' ⟶ S) :
    Polarization.FiberComparison.polarizationBiextensionMap D p f ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.snd (A.pullback f).scheme.hom (A.pullback f).scheme.hom ≫
        pullback.fst A.scheme.hom f := by
  let t := (Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme
  have ht : t.left ≫ pullback.snd (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom =
      pullback.snd (A.pullback f).scheme.hom (A.pullback f).scheme.hom :=
    (Over.tensorHom_left_snd _ _ _ _).trans (Category.comp_id _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => t.left ≫ a) (Pullback.Comparisons.poincareBaseChangeMap_snd D f)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ pullback.fst A.scheme.hom f) ht)))

/-- The comparison from an iterated fiber to the fiber of the composite map. -/
def Abelian.Schemes.AbelianScheme.fiberCompIso (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    ((A.pullback f).pullback h).scheme.left ≅ (A.pullback (h ≫ f)).scheme.left :=
  (Over.forget S'').mapIso (A.pullbackCompIso f h).symm

@[simp]
theorem Abelian.Schemes.AbelianScheme.fiberCompIso_hom (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.fiberCompIso f h).hom = (A.pullbackCompIso f h).inv.left := rfl

/-- The induced comparison on the square of the fiber. -/
def Abelian.Schemes.AbelianScheme.fiberProductCompIso (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    (((A.pullback f).pullback h).scheme ⊗ ((A.pullback f).pullback h).scheme).left ≅
      ((A.pullback (h ≫ f)).scheme ⊗ (A.pullback (h ≫ f)).scheme).left :=
  (Over.forget S'').mapIso ((A.pullbackCompIso f h).symm ⊗ᵢ (A.pullbackCompIso f h).symm)

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.fiberProductCompIso_hom_fst (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.fiberProductCompIso f h).hom ≫
        pullback.fst (A.pullback (h ≫ f)).scheme.hom (A.pullback (h ≫ f)).scheme.hom =
      pullback.fst ((A.pullback f).pullback h).scheme.hom ((A.pullback f).pullback h).scheme.hom ≫
        (A.fiberCompIso f h).hom :=
  Over.tensorHom_left_fst _ _ _ _

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.fiberProductCompIso_hom_snd (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.fiberProductCompIso f h).hom ≫
        pullback.snd (A.pullback (h ≫ f)).scheme.hom (A.pullback (h ≫ f)).scheme.hom =
      pullback.snd ((A.pullback f).pullback h).scheme.hom ((A.pullback f).pullback h).scheme.hom ≫
        (A.fiberCompIso f h).hom :=
  Over.tensorHom_left_snd _ _ _ _

/-- The fiber comparison respects the zero section. -/
theorem Abelian.Schemes.AbelianScheme.fiberCompIso_hom_one (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    η[((A.pullback f).pullback h).scheme].left ≫ (A.fiberCompIso f h).hom =
      η[(A.pullback (h ≫ f)).scheme].left :=
  congrArg (fun a => a.left) (IsMonHom.one_hom (A.pullbackCompIso f h).inv)

/-- The fiber comparison respects addition of points. -/
theorem Abelian.Schemes.AbelianScheme.fiberProductCompIso_hom_mul (A : Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.fiberProductCompIso f h).hom ≫ μ[(A.pullback (h ≫ f)).scheme].left =
      μ[((A.pullback f).pullback h).scheme].left ≫ (A.fiberCompIso f h).hom :=
  (congrArg (fun a => a.left) (IsMonHom.mul_hom (A.pullbackCompIso f h).inv)).symm

/-- The two constructions of the polarization map on an iterated fiber agree. -/
theorem Polarization.FiberComparison.polarizationBiextensionMap_comp (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    Polarization.FiberComparison.polarizationBiextensionMap (D.pullback f) ((Over.pullback f).map p) h ≫
        (D.poincarePullbackOverMap f).left =
      (A.fiberProductCompIso f h).hom ≫ Polarization.FiberComparison.polarizationBiextensionMap D p (h ≫ f) := by
  let B := ((A.pullback f).pullback h).scheme
  let C := (A.pullback (h ≫ f)).scheme
  let A₁ := (A.pullback f).scheme
  let D₁ := (D.abelian.pullback f).scheme
  let q : (B ⊗ B).left ⟶ (D₁ ⊗ A₁).left :=
    Polarization.FiberComparison.polarizationBiextensionMap (D.pullback f) ((Over.pullback f).map p) h
  let r : (D₁ ⊗ A₁).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    (D.poincarePullbackOverMap f).left
  let t : (C ⊗ C).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    Polarization.FiberComparison.polarizationBiextensionMap D p (h ≫ f)
  let e : (B ⊗ B).left ⟶ (C ⊗ C).left := (A.fiberProductCompIso f h).hom
  let a : B.left ⟶ C.left := (A.fiberCompIso f h).hom
  let b : B.left ⟶ A₁.left := pullback.fst A₁.hom h
  let c : A₁.left ⟶ A.scheme.left := pullback.fst A.scheme.hom f
  let d : C.left ⟶ A.scheme.left := pullback.fst A.scheme.hom (h ≫ f)
  let p₁ : A₁.left ⟶ D₁.left := ((Over.pullback f).map p).left
  let rD : D₁.left ⟶ D.abelian.scheme.left := pullback.fst D.abelian.scheme.hom f
  have hpf : p₁ ≫ rD = c ≫ p.left := Pullback.Comparisons.overPullback_map_left_fst p f
  have had : a ≫ d = b ≫ c := A.pullbackCompIso_inv_left_fst f h
  change q ≫ r = e ≫ t
  apply Over.tensorObj_ext
  · have hrf : r ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst D₁.hom A₁.hom ≫ rD := D.poincarePullbackOverMap_left_fst f
    have hqf : q ≫ pullback.fst D₁.hom A₁.hom =
        pullback.fst B.hom B.hom ≫ b ≫ p₁ :=
      Polarization.FiberComparison.polarizationBiextensionMap_fst (D.pullback f) ((Over.pullback f).map p) h
    have htf : t ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst C.hom C.hom ≫ d ≫ p.left := Polarization.FiberComparison.polarizationBiextensionMap_fst D p (h ≫ f)
    have hef : e ≫ pullback.fst C.hom C.hom = pullback.fst B.hom B.hom ≫ a :=
      A.fiberProductCompIso_hom_fst f h
    simp only [Category.assoc, hrf, reassoc_of% hqf, hpf, htf,
      reassoc_of% hef, reassoc_of% had]
  · have hrs : r ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd D₁.hom A₁.hom ≫ c := D.poincarePullbackOverMap_left_snd f
    have hqs : q ≫ pullback.snd D₁.hom A₁.hom =
        pullback.snd B.hom B.hom ≫ b :=
      Polarization.FiberComparison.polarizationBiextensionMap_snd (D.pullback f) ((Over.pullback f).map p) h
    have hts : t ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd C.hom C.hom ≫ d := Polarization.FiberComparison.polarizationBiextensionMap_snd D p (h ≫ f)
    have hes : e ≫ pullback.snd C.hom C.hom = pullback.snd B.hom B.hom ≫ a :=
      A.fiberProductCompIso_hom_snd f h
    simp only [Category.assoc, hrs, reassoc_of% hqs, hts,
      reassoc_of% hes, had]

/-- The actual polarization biextension on an iterated fiber is the pullback
of the biextension on the fiber of the composite map. -/
def Polarization.FiberComparison.polarizationBiextensionCompIso (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : S' ⟶ S) (h : S'' ⟶ S') :
    (PolarizationData.polarizationBiextensionAt (D.pullback f) ((Over.pullback f).map p) h).sheaf ≅
      (Line.Bundles.LineBundle.pullback (A.fiberProductCompIso f h).hom
        (PolarizationData.polarizationBiextensionAt D p (h ≫ f))).sheaf :=
  (Scheme.Modules.pullbackComp
    (Polarization.FiberComparison.polarizationBiextensionMap (D.pullback f) ((Over.pullback f).map p) h)
    (D.poincarePullbackOverMap f).left).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (Polarization.FiberComparison.polarizationBiextensionMap_comp D p f h)).app D.poincare.sheaf ≪≫
        (Scheme.Modules.pullbackComp (A.fiberProductCompIso f h).hom
          (Polarization.FiberComparison.polarizationBiextensionMap D p (h ≫ f))).symm.app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
