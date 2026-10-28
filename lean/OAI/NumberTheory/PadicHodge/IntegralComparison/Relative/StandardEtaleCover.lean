import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.StandardCover
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Standard Etale Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.StandardEtaleCover

noncomputable section

/-! An actual affine etale morphism has a source cover by standard
etale affine charts over any specified affine open cover of the base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsAffineHom f]
  (C : X.OpenCover.{v}) [∀ i, IsAffine (C.X i)]

abbrev sourceCover : Y.OpenCover.{v} := C.pullback₁ f
instance source_affine (i : C.I₀) : IsAffine ((sourceCover f C).X i) :=
  inferInstanceAs (IsAffine (pullback f (C.f i)))

abbrev baseRing (i : C.I₀) : CommRingCat.{u} := Γ(C.X i, ⊤)
abbrev sourceRing (i : C.I₀) : CommRingCat.{u} := Γ((sourceCover f C).X i, ⊤)

def sourceMap (i : C.I₀) : Spec (sourceRing f C i) ⟶ Y :=
  ((sourceCover f C).X i).isoSpec.inv ≫ (sourceCover f C).f i

instance sourceMap_open (i : C.I₀) : IsOpenImmersion (sourceMap f C i) := by
  unfold sourceMap
  infer_instance

instance sourceAlgebra (i : C.I₀) : Algebra (baseRing C i) (sourceRing f C i) :=
  (C.pullbackHom f i).appTop.hom.toAlgebra

instance sourceEtale (i : C.I₀) : Algebra.Etale (baseRing C i) (sourceRing f C i) := by
  let : Etale (C.pullbackHom f i) :=
    MorphismProperty.pullback_snd _ _ (inferInstanceAs (Etale f))
  change (C.pullbackHom f i).appTop.hom.Etale
  simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using
    (C.pullbackHom f i).etale_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)

omit [Etale f] in
theorem sourceMap_over (i : C.I₀) :
    sourceMap f C i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (baseRing C i) (sourceRing f C i))) ≫
      (C.X i).isoSpec.inv ≫ C.f i := by
  change (_ ≫ (sourceCover f C).f i) ≫ f = Spec.map (C.pullbackHom f i).appTop ≫ _
  rw [Category.assoc, ← C.pullbackHom_map f i, ← Category.assoc,
    ← Scheme.isoSpec_inv_naturality, Category.assoc]

abbrev Index := Σ i : C.I₀, IntegralComparison.Etale.StandardCover.localizers (baseRing C i) (sourceRing f C i)

abbrev coordinateRing (a : Index f C) : CommRingCat.{u} := CommRingCat.of (Localization.Away a.2.val)

instance coordinateAlgebra (a : Index f C) : Algebra (baseRing C a.1) (coordinateRing f C a) :=
  inferInstanceAs (Algebra (baseRing C a.1) (Localization.Away a.2.val))

instance coordinateStandard (a : Index f C) : Algebra.IsStandardEtale (baseRing C a.1) (coordinateRing f C a) :=
  IntegralComparison.Etale.StandardCover.standard (baseRing C a.1) (sourceRing f C a.1) a.2

def presentation (a : Index f C) : StandardEtalePresentation (baseRing C a.1) (coordinateRing f C a) :=
  IntegralComparison.Etale.StandardCover.presentation (baseRing C a.1) (sourceRing f C a.1) a.2

def localizationMap (a : Index f C) : sourceRing f C a.1 ⟶ coordinateRing f C a :=
  CommRingCat.ofHom (algebraMap (sourceRing f C a.1) (Localization.Away a.2.val))

def chartMap (a : Index f C) : Spec (coordinateRing f C a) ⟶ Y :=
  Spec.map (localizationMap f C a) ≫ sourceMap f C a.1

instance chartMap_open (a : Index f C) : IsOpenImmersion (chartMap f C a) := by
  let : IsOpenImmersion (Spec.map (localizationMap f C a)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (sourceRing f C a.1) (Localization.Away a.2.val)))))
  unfold chartMap
  infer_instance

theorem chartMap_over (a : Index f C) : chartMap f C a ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap (baseRing C a.1) (coordinateRing f C a))) ≫
      (C.X a.1).isoSpec.inv ≫ C.f a.1 := by
  rw [chartMap, Category.assoc, sourceMap_over, ← Category.assoc, ← Spec.map_comp]
  congr 2

theorem covers (y : Y) : ∃ a : Index f C, y ∈ Set.range (chartMap f C a) := by
  obtain ⟨i, z, hz⟩ := Scheme.Cover.exists_eq (sourceCover f C) y
  change C.I₀ at i
  let D := Scheme.affineOpenCoverOfSpanRangeEqTop
    (fun a : IntegralComparison.Etale.StandardCover.localizers (baseRing C i) (sourceRing f C i) => a.val)
    (IntegralComparison.Etale.StandardCover.span (baseRing C i) (sourceRing f C i))
  obtain ⟨a, t, ht⟩ := Scheme.Cover.exists_eq D.openCover (((sourceCover f C).X i).isoSpec.hom z)
  change (D.f a) t = ((sourceCover f C).X i).isoSpec.hom z at ht
  refine ⟨⟨i, a⟩, t, ?_⟩
  change (sourceCover f C).f i (((sourceCover f C).X i).isoSpec.inv ((D.f a) t)) = y
  rw [ht]
  have he := congrArg (fun g : (sourceCover f C).X i ⟶ (sourceCover f C).X i => g z)
    (((sourceCover f C).X i).isoSpec.hom_inv_id)
  change ((sourceCover f C).X i).isoSpec.inv (((sourceCover f C).X i).isoSpec.hom z) = z at he
  rw [he]
  exact hz

def cover : Y.OpenCover where
  I₀ := Index f C
  X a := Spec (coordinateRing f C a)
  f := chartMap f C
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨covers f C, inferInstance⟩

def presentedMap (a : Index f C) : Spec (.of (presentation f C a).P.Ring) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (presentation f C a).equivRing.toRingHom) ≫ chartMap f C a

instance presentedMap_open (a : Index f C) : IsOpenImmersion (presentedMap f C a) := by
  let : IsIso (Spec.map (CommRingCat.ofHom (presentation f C a).equivRing.toRingHom)) :=
    (Scheme.Spec.mapIso (presentation f C a).equivRing.toCommRingCatIso.op).isIso_hom
  unfold presentedMap
  infer_instance

theorem presentedMap_over (a : Index f C) : presentedMap f C a ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap (baseRing C a.1) (presentation f C a).P.Ring)) ≫
      (C.X a.1).isoSpec.inv ≫ C.f a.1 := by
  rw [presentedMap, Category.assoc, chartMap_over, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact (presentation f C a).equivRing.commutes r

theorem presented_covers (y : Y) : ∃ a : Index f C, y ∈ Set.range (presentedMap f C a) := by
  obtain ⟨a, z, hz⟩ := covers f C y
  let e := Scheme.Spec.mapIso (presentation f C a).equivRing.toCommRingCatIso.op
  refine ⟨a, e.inv z, ?_⟩
  change (chartMap f C a) (e.hom (e.inv z)) = y
  have he := congrArg (fun g : Spec (coordinateRing f C a) ⟶ Spec (coordinateRing f C a) => g z)
    e.inv_hom_id
  change e.hom (e.inv z) = z at he
  rw [he]
  exact hz

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.StandardEtaleCover
