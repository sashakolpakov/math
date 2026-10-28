import Mathlib
import OAI.AlgebraicGeometry.SheafCohomology.API

/-! # Zero Outside -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside

noncomputable section

open _root_.TopCat

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false

namespace ProjectiveVanishing.TopCat

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Extension-by-zero presheaf and sheaf machinery

The "extension by zero" of a presheaf `F` along the inclusion of an open `U`. The
construction `zeroOutside U F` agrees with `F` on opens `W ≤ U` and is the zero object
elsewhere. Sheafified, with `F = constZ` (the constant presheaf with value `ULift ℤ`), this
yields `zeroOutsideInt U`, which serves as the canonical generator family for the
finitely-generated subsheaf reduction in the Grothendieck vanishing proof.

## Main definitions

* `TopCat.Presheaf.zeroOutside` — the extension-by-zero presheaf.
* `TopCat.Presheaf.constZ` — the constant presheaf `ULift ℤ`.
* `TopCat.Sheaf.zeroOutsideInt` — sheafified extension-by-zero of `constZ` on `U`.
* `TopCat.Sheaf.zeroOutsideInt.sHom` — section-to-morphism construction.
* `TopCat.Sheaf.zeroOutsideInt.generator` — canonical generator of
 `((TopCat.Presheaf.zeroOutside U constZ)).obj (op U)`.

## Main results

* `zeroOutside_openHom_stalk_surj`, `sheafifyMap_zeroOutside_openHom_stalk_surj` — stalk
 surjectivity for the open-inclusion morphisms (and their sheafifications) at points of
 the support.
* `stalk_zeroOutsideInt_zero_outside` — stalks of `zeroOutsideInt U` vanish off `U`.
* `isZero_zeroOutsideInt_bot` — `zeroOutsideInt ⊥` is the zero sheaf.
* `stalk_zeroOutsideInt_eq_zsmul_generator` — stalks on `U` are integer multiples of the
 canonical germ.
-/

universe u

open Limits

namespace Presheaf
open _root_.TopCat.Presheaf

open ZeroObject ConcreteCategory

section

variable {C : Type*} [Category C] [HasZeroObject C] {X : TopCat.{u}}
    (U : Opens X) (F : Presheaf C X)

open Classical in
def zeroOutside : Presheaf C X where
  obj W := if (unop W) ≤ U then F.obj W else 0
  map {W Y} i :=
    if h : (unop W) ≤ U then
      eqToHom (by grind) ≫ F.map i ≫ eqToHom (by rw [ite_eq_left (le_trans (leOfHom i.unop) h)])
    else ((ite_eq_right h).symm.ndrec (isZero_zero C)).to_ _
  map_id W := by
    split_ifs with h
    · simp
    · apply IsZero.to_eq
  map_comp {W Y Z} iWY iYZ := by
    split_ifs with h
    · have : unop Y ≤ U := le_trans (leOfHom iWY.unop) h
      have : unop Z ≤ U := le_trans (leOfHom iYZ.unop) this
      simp_all
    · apply IsZero.to_eq

variable {U F}

lemma zeroOutside_isZero {W : Opens X} (h : ¬ W ≤ U) :
    IsZero ((zeroOutside U F).obj (op W)) := by
  simp [zeroOutside, h, isZero_zero C]

lemma zeroOutside_le {W : Opens X} (h : W ≤ U) :
    (zeroOutside U F).obj (op W) = F.obj (op W) := by
  simp [zeroOutside, h]

/-- `zeroOutside ⊤ F ≅ F`: zero-outside on the whole space is the identity. -/
def zeroOutside_top_iso : zeroOutside (⊤ : Opens X) F ≅ F :=
  NatIso.ofComponents
    (fun W ↦ eqToIso (zeroOutside_le (le_top : unop W ≤ ⊤)))
    (fun {W Y} i ↦ by simp [zeroOutside, le_top])

variable {V : Opens X} (h : V ≤ U)

open Classical in
def zeroOutside_openHom [HasPullbacks C] : zeroOutside V F ⟶ zeroOutside U F where
  app W := if hW : (unop W) ≤ V then
      eqToHom (by rw [zeroOutside_le hW, zeroOutside_le (le_trans hW h)])
    else (zeroOutside_isZero (F := F) hW).to_ _
  naturality {W Y} i := by
    by_cases hWV : (unop W) ≤ V
    · have hYV : unop Y ≤ V := le_trans (leOfHom i.unop) hWV
      have hYU : unop Y ≤ U := le_trans hYV h
      have hWU : unop W ≤ U := le_trans hWV h
      simp [zeroOutside, hWV, hYV, hWU, hYU]
    · apply (zeroOutside_isZero (F := F) hWV).eq_of_src

instance zeroOutside_hom_mono [HasPullbacks C] : Mono (zeroOutside_openHom (F := F) h) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W; by_cases hWV : (unop W) ≤ V
  · have hWU : unop W ≤ U := le_trans hWV h
    simp [zeroOutside_openHom, hWV, IsIso.mono_of_iso]
  · simp [zeroOutside_openHom, hWV, zeroOutside_isZero (F := F) hWV, IsZero.mono]

/-- The presheaf stalk map of `zeroOutside_openHom h` at `x ∈ V` is surjective:
 any germ in the larger zero-outside presheaf can be lifted by restricting to `W ∩ V ≤ V`
 where the presheaf map is `eqToHom` (identity). -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside.ProjectiveVanishing.zeroOutside_openHom_stalk_surj
    {X : TopCat.{u}} {F : TopCat.Presheaf AddCommGrpCat.{u} X}
    {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (zeroOutside_openHom (F := F) h))) := by
  intro g
  obtain ⟨W, hxW, s, rfl⟩ := (zeroOutside U F).exists_germ_eq g
  set WV := W ⊓ V
  have hWV_le_V : WV ≤ V := inf_le_right
  have hWV_le_W : WV ≤ W := inf_le_left
  have hxWV : x ∈ WV := ⟨hxW, hx⟩
  have happ_iso : IsIso ((zeroOutside_openHom (F := F) h).app (op WV)) := by
    simp only [zeroOutside_openHom, hWV_le_V, ↓reduceDIte]
    infer_instance
  let s_res := ConcreteCategory.hom (((zeroOutside U F)).map (homOfLE hWV_le_W).op) s
  have h_bij := ConcreteCategory.bijective_of_isIso
    ((zeroOutside_openHom (F := F) h).app (op WV))
  obtain ⟨t, ht⟩ := h_bij.2 s_res
  refine ⟨((zeroOutside V F)).germ WV x hxWV t, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change ((zeroOutside U F)).germ WV x hxWV
      ((zeroOutside_openHom (F := F) h).app (op WV) t) =
    ((zeroOutside U F)).germ W x hxW s
  rw [ht]
  simp only [s_res]
  convert (((zeroOutside U F)).germ_res_apply (homOfLE hWV_le_W) x hxWV s) using 1

/-- The sheaf stalk map of `sheafifyMap (zeroOutside_openHom h)` at `x ∈ V` is surjective.
 Transfers presheaf stalk surjectivity via `toSheafify_naturality` and
 the fact that `stalk(toSheafify)` is an isomorphism. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside.ProjectiveVanishing.sheafifyMap_zeroOutside_openHom_stalk_surj
    {X : TopCat.{u}} (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {V U : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (sheafifyMap (Opens.grothendieckTopology (T := X))
          (zeroOutside_openHom (F := F) h)))) := by
  let J := Opens.grothendieckTopology (T := X)
  let φ := zeroOutside_openHom (F := F) h
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let ηV := CategoryTheory.toSheafify J ((zeroOutside V F))
  let ηU := CategoryTheory.toSheafify J ((zeroOutside U F))
  have hnat : T.map φ ≫ T.map ηU =
      T.map ηV ≫ T.map (CategoryTheory.sheafifyMap J φ) := by
    dsimp [ηV, ηU]
    rw [← T.map_comp, ← T.map_comp, CategoryTheory.toSheafify_naturality]
  have : IsIso (T.map ηV) :=
    ClosedImmersion.ProjectiveVanishing.TopCat.stalkFunctor_map_iso_toSheafify _ x
  have : IsIso (T.map ηU) :=
    ClosedImmersion.ProjectiveVanishing.TopCat.stalkFunctor_map_iso_toSheafify _ x
  intro g
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map ηU)).2 g
  obtain ⟨p, hp⟩ := zeroOutside_openHom_stalk_surj h x hx q
  exact ⟨ConcreteCategory.hom (T.map ηV) p, by
    change ConcreteCategory.hom (T.map (CategoryTheory.sheafifyMap J φ))
        (ConcreteCategory.hom (T.map ηV) p) = _
    rw [← ConcreteCategory.comp_apply, hnat.symm, ConcreteCategory.comp_apply, hp]⟩

end

open _root_.AddCommGrpCat

abbrev constZ {X : TopCat.{u}} : Presheaf AddCommGrpCat.{u} X :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))

namespace zeroOutside

variable {X : TopCat.{u}} (U : Opens X)

def generator : ((zeroOutside U constZ)).obj (op U) :=
  (eqToHom (by simp [zeroOutside, constZ]) : AddCommGrpCat.of (ULift ℤ) ⟶ ((zeroOutside U constZ)).obj (op U)) 1

variable {U}

open Classical in
def sHom {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    (zeroOutside U constZ) ⟶ F where
  app {W} :=
    if h : (unop W) ≤ U then
      eqToHom (by simp_all [zeroOutside, constZ]) ≫
        AddCommGrpCat.ofHom (uliftZMultiplesHom (F.obj W) (F.map (homOfLE h).op s))
    else 0
  naturality {W Y} i := by
    by_cases hWU : (unop W) ≤ U
    · have hYU : (unop Y) ≤ U := le_trans (leOfHom i.unop) hWU
      apply AddCommGrpCat.hom_ext
      ext z
      have hmap :
          F.map (homOfLE hYU).op s = F.map i (F.map (homOfLE hWU).op s) := by
        simpa [Functor.map_comp_apply] using
          (congrArg (fun j ↦ F.map j s) (Subsingleton.elim ((homOfLE hWU).op ≫ i)
            (homOfLE hYU).op)).symm
      have hObjW : (zeroOutside U constZ).obj W = AddCommGrpCat.of (ULift ℤ) := by
        simp [zeroOutside, hWU, constZ]
      let w : ULift ℤ :=
        (AddCommGrpCat.Hom.hom (eqToHom hObjW) z)
      have hz : (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) w = z := by
        simp [w, ← ConcreteCategory.comp_apply, eqToHom_trans]
      rw [← hz]
      simp [zeroOutside, hWU, hYU, w, hmap, constZ]
    · apply (zeroOutside_isZero (F := constZ) hWU).eq_of_src

theorem sHom_app_generator {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    (sHom s).app (op U) (generator U) = s := by
  have hObjU : (zeroOutside U constZ).obj (op U) = AddCommGrpCat.of (ULift ℤ) := by
    simp [zeroOutside, constZ]
  have h1 :
      (AddCommGrpCat.Hom.hom (eqToHom hObjU))
          ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ)) = (1 : ULift ℤ) := by
    simp [← comp_apply, eqToHom_trans]
  have hgen : generator U =
      (eqToHom hObjU.symm :
        AddCommGrpCat.of (ULift ℤ) ⟶ (zeroOutside U constZ).obj (op U)) (1 : ULift ℤ) := by
    simp [generator]
  rw [hgen]
  simp [sHom, zeroOutside, constZ]
  change (((AddCommGrpCat.Hom.hom (eqToHom hObjU))
      ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ))).down : ℤ) • s = s
  rw [congrArg ULift.down h1]
  simp

/-- The restriction of the distinguished generator of `(TopCat.Presheaf.zeroOutside V constZ)` to a smaller open
`W ≤ V` corresponds to `1: ULift ℤ` under the canonical identification with `ULift ℤ`. -/
theorem resGen_eqToHom_eq_one
    {X : TopCat.{u}} (V : Opens X) {W : Opens X} (hWV : W ≤ V)
    (hObjW : ((zeroOutside V constZ)).obj (op W) = AddCommGrpCat.of (ULift ℤ)) :
    (AddCommGrpCat.Hom.hom (eqToHom hObjW))
      (ConcreteCategory.hom (((zeroOutside V constZ)).map (homOfLE hWV).op)
        (generator V)) = (1 : ULift ℤ) := by
  unfold generator
  simp only [zeroOutside, dite_eq_left (le_refl V),
    ← ConcreteCategory.comp_apply, Functor.const_obj_map]
  simp

/-- At a point inside the support open, every stalk element of the presheaf `(TopCat.Presheaf.zeroOutside V constZ)`
is an integer multiple of the germ of the distinguished generator over `V`. -/
theorem presheaf_stalk_zeroOutside_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((zeroOutside V constZ))) :
    ∃ n : ℤ,
      a = n • (((zeroOutside V constZ)).germ V x hx (generator V)) := by
  obtain ⟨W, hxW, s, rfl⟩ := (zeroOutside V constZ).exists_germ_eq a
  by_cases hWV : W ≤ V
  · have hObjW : (zeroOutside V constZ).obj (op W) =
        AddCommGrpCat.of (ULift ℤ) := by
      simp [zeroOutside, hWV, constZ]
    let w : ULift ℤ := (AddCommGrpCat.Hom.hom (eqToHom hObjW)) s
    let genW : ((zeroOutside V constZ)).obj (op W) :=
      ConcreteCategory.hom (((zeroOutside V constZ)).map (homOfLE hWV).op) (generator V)
    have hgenW_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) genW = (1 : ULift ℤ) :=
      resGen_eqToHom_eq_one V hWV hObjW
    have hinj : Function.Injective (AddCommGrpCat.Hom.hom (eqToHom hObjW)) :=
      (ConcreteCategory.bijective_of_isIso (eqToHom hObjW)).1
    have hs_zsmul : s = w.down • genW := by
      apply hinj
      rw [map_zsmul, hgenW_val]
      show w = w.down • (1 : ULift ℤ)
      ext
      simp
    refine ⟨w.down, ?_⟩
    rw [hs_zsmul, map_zsmul (ConcreteCategory.hom (((zeroOutside V constZ)).germ W x hxW))]
    congr 1
    exact TopCat.Presheaf.germ_res_apply ((zeroOutside V constZ))
      (homOfLE hWV) x hxW (generator V)
  · have hIsZero := zeroOutside_isZero (F := constZ) hWV
    have := AddCommGrpCat.subsingleton_of_isZero hIsZero
    exact ⟨0, by simp [Subsingleton.eq_zero s, map_zero]⟩

end zeroOutside

end Presheaf

namespace Sheaf
open _root_.TopCat.Sheaf

open Presheaf

def _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt {X : TopCat.{u}} (U : Opens X) : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf _ _).obj ((ProjectiveVanishing.TopCat.Presheaf.zeroOutside U ProjectiveVanishing.TopCat.Presheaf.constZ))

namespace zeroOutsideInt

variable {X : TopCat.{u}} (U : Opens X)

def _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator : (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt U).obj.obj (op U) :=
  (toSheafify _ ((ProjectiveVanishing.TopCat.Presheaf.zeroOutside U ProjectiveVanishing.TopCat.Presheaf.constZ))).app (op U) (ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator U)

variable {U}

@[simps]
def _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V ⟶ Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt U where
  hom := sheafifyMap _ (ProjectiveVanishing.TopCat.Presheaf.zeroOutside_openHom (F := ProjectiveVanishing.TopCat.Presheaf.constZ) h)

instance {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) : Mono (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom h) := by
  have := ProjectiveVanishing.TopCat.Presheaf.zeroOutside_hom_mono
    (F := (Functor.const _).obj (AddCommGrpCat.of (ULift.{u, 0} ℤ))) h
  delta Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom
  apply Functor.map_mono (presheafToSheaf _ _)

abbrev _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHomVal {X : TopCat.{u}} {U : Opens X} {F : Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (s : F.obj (op U)) : (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt U).obj ⟶ F :=
  sheafifyLift _ (ProjectiveVanishing.TopCat.Presheaf.zeroOutside.sHom s) hF

def _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHom {X : TopCat.{u}} {U : Opens X} {F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X}
    (s : F.obj.obj (op U)) : Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt U ⟶ F where
  hom := Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHomVal F.property s

theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHomVal_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (s : F.obj (op U)) :
    (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHomVal hF s).app (op U) (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator U) = s := by
  delta Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, toSheafify_sheafifyLift]
  exact ProjectiveVanishing.TopCat.Presheaf.zeroOutside.sHom_app_generator s

theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHom_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X} (s : F.obj.obj (op U)) :
    (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHom s).hom.app (op U) (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator U) = s := by
  exact Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHomVal_app_generator F.property s

theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom_val_app_generator {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom h).hom.app (op V) (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator V) =
    (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt U).obj.map (homOfLE h).op (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator U) := by
  delta Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator
  erw [Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom_hom,
    ← ConcreteCategory.comp_apply
      ((CategoryTheory.toSheafify _ ((ProjectiveVanishing.TopCat.Presheaf.zeroOutside V ProjectiveVanishing.TopCat.Presheaf.constZ))).app (op V))
      ((CategoryTheory.sheafifyMap _ (ProjectiveVanishing.TopCat.Presheaf.zeroOutside_openHom (F := ProjectiveVanishing.TopCat.Presheaf.constZ) h)).app
        (op V)),
    ← NatTrans.comp_app (CategoryTheory.toSheafify _ ((ProjectiveVanishing.TopCat.Presheaf.zeroOutside V ProjectiveVanishing.TopCat.Presheaf.constZ)))
      (CategoryTheory.sheafifyMap _ (ProjectiveVanishing.TopCat.Presheaf.zeroOutside_openHom (F := ProjectiveVanishing.TopCat.Presheaf.constZ) h)),
    ← CategoryTheory.toSheafify_naturality _ (ProjectiveVanishing.TopCat.Presheaf.zeroOutside_openHom (F := ProjectiveVanishing.TopCat.Presheaf.constZ) h),
    NatTrans.comp_app, ConcreteCategory.comp_apply,
    ← (CategoryTheory.toSheafify _ ((ProjectiveVanishing.TopCat.Presheaf.zeroOutside U ProjectiveVanishing.TopCat.Presheaf.constZ))).naturality_apply
      (homOfLE h).op (ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator U)]
  congr 1
  simp [ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator, ProjectiveVanishing.TopCat.Presheaf.zeroOutside_openHom, h,
    ProjectiveVanishing.TopCat.Presheaf.zeroOutside, ProjectiveVanishing.TopCat.Presheaf.constZ, ← ConcreteCategory.comp_apply, eqToHom_trans]

end zeroOutsideInt

open zeroOutsideInt

/-- Stalks of `zeroOutsideInt V` vanish outside `V`. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside.ProjectiveVanishing.stalk_zeroOutsideInt_zero_outside
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∉ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj) : a = 0 := by
  let P := (ProjectiveVanishing.TopCat.Presheaf.zeroOutside V ProjectiveVanishing.TopCat.Presheaf.constZ)
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (T.map (toSheafify J P)) := ClosedImmersion.ProjectiveVanishing.TopCat.stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨W, hxW, s, rfl⟩ := P.exists_germ_eq q
  have := AddCommGrpCat.subsingleton_of_isZero
    (ProjectiveVanishing.TopCat.Presheaf.zeroOutside_isZero (F := ProjectiveVanishing.TopCat.Presheaf.constZ) (fun h ↦ hx (h hxW)))
  simp [Subsingleton.eq_zero s, map_zero]

/-- `zeroOutsideInt ⊥` is the zero sheaf (all stalks vanish). -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside.ProjectiveVanishing.isZero_zeroOutsideInt_bot (X : TopCat.{u}) :
    IsZero (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)) := by
  let F := Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt (⊥ : Opens X)
  change IsZero F
  have hstalk :
      ∀ (x : X) (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.obj), a = 0 := by
    intro x a
    exact stalk_zeroOutsideInt_zero_outside ⊥ x (Opens.mem_bot.not.mpr (fun h ↦ h.elim)) a
  exact API.ProjectiveVanishing.sheaf_isZero_of_zero_stalks X F.property hstalk

/-- At a point inside the support open, every stalk element of `zeroOutsideInt V` is an integer
 multiple of the germ of the distinguished generator over `V`. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside.ProjectiveVanishing.stalk_zeroOutsideInt_eq_zsmul_generator
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj) :
    ∃ n : ℤ,
      a = n • ((_root_.TopCat.Presheaf.germ (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj) V x hx
        (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator V)) := by
  let P := (ProjectiveVanishing.TopCat.Presheaf.zeroOutside V ProjectiveVanishing.TopCat.Presheaf.constZ)
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (T.map (toSheafify J P)) := ClosedImmersion.ProjectiveVanishing.TopCat.stalkFunctor_map_iso_toSheafify P x
  obtain ⟨q, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))).2 a
  obtain ⟨n, hn⟩ :=
    ProjectiveVanishing.TopCat.Presheaf.zeroOutside.presheaf_stalk_zeroOutside_eq_zsmul_generator V x hx q
  refine ⟨n, ?_⟩
  rw [hn, map_zsmul]
  congr 1
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
    (toSheafify J P) (ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator V)

/-- The map `n ↦ n • gen` from `ℤ` into `stalk(zeroOutsideInt V, x)` is injective
 for `x ∈ V`. -/
theorem _root_.OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside.ProjectiveVanishing.zsmul_generator_injective
    {X : TopCat.{u}} (V : Opens X) (x : X) (hx : x ∈ V) :
    Function.Injective (fun (n : ℤ) ↦
      n • ((_root_.TopCat.Presheaf.germ (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj) V x hx
        (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator V))) := by
  intro n m h
  let P := (ProjectiveVanishing.TopCat.Presheaf.zeroOutside V ProjectiveVanishing.TopCat.Presheaf.constZ)
  let J := Opens.grothendieckTopology (T := X)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : IsIso (T.map (toSheafify J P)) := ClosedImmersion.ProjectiveVanishing.TopCat.stalkFunctor_map_iso_toSheafify P x
  have hbij := ConcreteCategory.bijective_of_isIso (T.map (toSheafify J P))
  have hgen_eq : ConcreteCategory.hom (T.map (toSheafify J P))
      (P.germ V x hx (ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator V)) =
      (_root_.TopCat.Presheaf.germ (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj) V x hx
        (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator V) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V x hx
      (toSheafify J P) (ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator V)
  set gen_P := ProjectiveVanishing.TopCat.Presheaf.zeroOutside.generator V
  have h' : P.germ V x hx (n • gen_P) = P.germ V x hx (m • gen_P) := by
    rw [map_zsmul, map_zsmul]
    apply hbij.1
    simp only [map_zsmul, hgen_eq]
    exact h
  obtain ⟨W, hxW, iU, iV, hEq⟩ := P.germ_eq x hx hx _ _ h'
  rw [Subsingleton.elim iU iV, map_zsmul, map_zsmul] at hEq
  have hWV : W ≤ V := leOfHom iV
  rw [Subsingleton.elim iV (homOfLE hWV)] at hEq
  have hObjW : P.obj (op W) = AddCommGrpCat.of (ULift ℤ) := by
    simp [P, ProjectiveVanishing.TopCat.Presheaf.zeroOutside, hWV, ProjectiveVanishing.TopCat.Presheaf.constZ]
  set resGen := ConcreteCategory.hom (P.map (homOfLE hWV).op) gen_P
  have hresGen_val : (AddCommGrpCat.Hom.hom (eqToHom hObjW)) resGen = (1 : ULift ℤ) :=
    ProjectiveVanishing.TopCat.Presheaf.zeroOutside.resGen_eqToHom_eq_one V hWV hObjW
  have hEq_ULift : n • (1 : ULift ℤ) = m • (1 : ULift ℤ) := by
    have := congrArg (AddCommGrpCat.Hom.hom (eqToHom hObjW)) hEq
    rwa [map_zsmul, map_zsmul, hresGen_val] at this
  simpa using congrArg ULift.down hEq_ULift

end Sheaf

end ProjectiveVanishing.TopCat

end

end OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside
