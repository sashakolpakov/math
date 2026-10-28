import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.OrientationCoefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Sheaf Orientation Coefficients -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.SheafOrientationCoefficients

noncomputable section

section

/-! Normal coefficients on every ambient open set retain all restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X S : TopCat.{0}}
variable (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (f : S ⟶ X)
variable (e : ∀ x, F.presheaf.stalk (f x) ≅ ModuleCat.of ℚ ℚ)
variable (σ : F.obj.obj (op (⊤ : Opens X)))
variable (hσ : ∀ x, Chern.Sheaf.OrientationCoefficients.sheafOrientationCoefficient F f e σ x = 1)

def openSheafOrientationCoefficient (U : Opens X) (s : F.obj.obj (op U))
    (x : (Opens.map f).obj U) : ℚ :=
  (e x.val).hom (F.presheaf.germ U (f x.val) x.property s)

include σ hσ in
theorem openSheafOrientationCoefficient_locallyConstant (U : Opens X)
    (s : F.obj.obj (op U)) : IsLocallyConstant (openSheafOrientationCoefficient F f e U s) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  let q := openSheafOrientationCoefficient F f e U s x
  have hg : F.presheaf.germ U (f x.val) x.property s =
      F.presheaf.germ ⊤ (f x.val) trivial (q • σ) := by
    apply (e x.val).toLinearEquiv.injective
    change q = (e x.val).hom (F.presheaf.germ ⊤ (f x.val) trivial (q • σ))
    rw [map_smul, map_smul]
    change q = q * Chern.Sheaf.OrientationCoefficients.sheafOrientationCoefficient F f e σ x.val
    rw [hσ, mul_one]
  obtain ⟨W, hx, i, j, hw⟩ := F.presheaf.germ_eq (U := U) (V := ⊤)
    (f x.val) x.property trivial s (q • σ) hg
  refine ⟨(fun y : (Opens.map f).obj U => f y.val) ⁻¹' (W : Set X),
    W.isOpen.preimage (f.hom.continuous.comp continuous_subtype_val), hx, ?_⟩
  intro y hy
  have hy' := congrArg (F.presheaf.germ W (f y.val) hy) hw
  simp only [TopCat.Presheaf.germ_res_apply] at hy'
  have hc := congrArg (e y.val).hom hy'
  rw [map_smul, map_smul] at hc
  change openSheafOrientationCoefficient F f e U s y =
    q * Chern.Sheaf.OrientationCoefficients.sheafOrientationCoefficient F f e σ y.val at hc
  simpa only [hσ, mul_one] using hc

def supportLocallyConstantPresheaf : X.Presheaf (ModuleCat.{0} ℚ) :=
  (TopCat.Presheaf.pushforward (ModuleCat.{0} ℚ) f).obj
    (Cech.Obj.RationalCech.locallyConstantPresheaf S)

def openSheafOrientationCoefficients (U : Opens X) :
    F.obj.obj (op U) →ₗ[ℚ] LocallyConstant ((Opens.map f).obj U) ℚ where
  toFun s := ⟨openSheafOrientationCoefficient F f e U s,
    openSheafOrientationCoefficient_locallyConstant F f e σ hσ U s⟩
  map_add' s t := by
    apply LocallyConstant.ext
    intro x
    exact map_add ((F.presheaf.germ U (f x.val) x.property) ≫ (e x.val).hom).hom s t
  map_smul' q s := by
    apply LocallyConstant.ext
    intro x
    exact map_smul ((F.presheaf.germ U (f x.val) x.property) ≫ (e x.val).hom).hom q s

def orientationCoefficientsPresheafMap : F.obj ⟶ supportLocallyConstantPresheaf f where
  app U := ModuleCat.ofHom (openSheafOrientationCoefficients F f e σ hσ U.unop)
  naturality U W i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply LocallyConstant.ext
    intro x
    change (e x.val).hom (F.presheaf.germ W.unop (f x.val) x.property (F.obj.map i s)) =
      (e x.val).hom (F.presheaf.germ U.unop (f x.val) _ s)
    exact congrArg (e x.val).hom
      (TopCat.Presheaf.germ_res_apply F.presheaf i.unop (f x.val) x.property s)

theorem openSheafOrientationCoefficients_injective
    (hz : ∀ y, y ∉ Set.range f → IsZero (F.presheaf.stalk y)) (U : Opens X) :
    Function.Injective (openSheafOrientationCoefficients F f e σ hσ U) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F U
  intro y hyU
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    apply (e x).toLinearEquiv.injective
    exact congrArg (fun g : LocallyConstant ((Opens.map f).obj U) ℚ => g ⟨x, hyU⟩) h
  · exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hz y hy)) _ _

end

/-! The actual normal coefficients give an isomorphism on every open set. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X S : TopCat.{0}}
variable (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (f : S ⟶ X)
variable (e : ∀ x, F.presheaf.stalk (f x) ≅ ModuleCat.of ℚ ℚ)
variable (σ : F.obj.obj (op (⊤ : Opens X)))
variable (hσ : ∀ x, Chern.Sheaf.OrientationCoefficients.sheafOrientationCoefficient F f e σ x = 1)

theorem openSheafOrientationCoefficients_surjective (hf : Topology.IsClosedEmbedding f)
    (hz : ∀ y, y ∉ Set.range f → IsZero (F.presheaf.stalk y)) (U : Opens X) :
    Function.Surjective (openSheafOrientationCoefficients F f e σ hσ U) := by
  intro g
  let T := (Opens.map f).obj U
  have hind : Topology.IsInducing (fun x : T => f x.val) :=
    hf.isInducing.comp Topology.IsInducing.subtypeVal
  have hopen (x : T) : ∃ W : Opens X,
      W ≤ U ∧ f x.val ∈ W ∧ ∀ y : T, f y.val ∈ W → g y = g x := by
    obtain ⟨W, hW, heq⟩ := hind.isOpen_iff.mp (g.isLocallyConstant.isOpen_fiber (g x))
    refine ⟨⟨W, hW⟩ ⊓ U, inf_le_right, ?_, ?_⟩
    · refine ⟨?_, x.property⟩
      change x ∈ (fun z : T => f z.val) ⁻¹' W
      rw [heq]
      rfl
    · intro y hy
      have : y ∈ (fun z : T => f z.val) ⁻¹' W := hy.1
      rwa [heq] at this
  choose W hWU hx hval using hopen
  let O : Opens X := U ⊓ ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  let V : Option T → Opens X
    | none => O
    | some x => W x
  have hVU (i : Option T) : V i ≤ U := by
    cases i with
    | none => exact inf_le_left
    | some x => exact hWU x
  let a : (i : Option T) → F.obj.obj (op (V i))
    | none => 0
    | some x => g x • F.obj.map (homOfLE (le_top : W x ≤ ⊤)).op σ
  have hcover : U ≤ iSup V := by
    intro y hyU
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      exact (le_iSup V (some ⟨x, hyU⟩)) (hx ⟨x, hyU⟩)
    · exact (le_iSup V none) ⟨hyU, hy⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V a := by
    apply AlgebraicTopology.Cohomology.Singular.SheafGluing.moduleSheaf_compatible_of_germs F V a
    intro i j y hi hj
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      cases i with
      | none => exact False.elim (hi.2 ⟨x, rfl⟩)
      | some i =>
        cases j with
        | none => exact False.elim (hj.2 ⟨x, rfl⟩)
        | some j =>
          let z : T := ⟨x, hWU i hi⟩
          have hij : g i = g j := (hval i z hi).symm.trans (hval j z hj)
          change F.presheaf.germ (W i) (f x) hi
              (g i • F.obj.map (homOfLE (le_top : W i ≤ ⊤)).op σ) =
            F.presheaf.germ (W j) (f x) hj
              (g j • F.obj.map (homOfLE (le_top : W j ≤ ⊤)).op σ)
          simp only [map_smul, TopCat.Presheaf.germ_res_apply, hij]
    · exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (hz y hy)) _ _
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcover a hcompat
  refine ⟨s, ?_⟩
  apply LocallyConstant.ext
  intro x
  change openSheafOrientationCoefficient F f e U s x = g x
  have hg := congrArg (F.presheaf.germ (W x) (f x.val) (hx x)) (hs (some x))
  change F.presheaf.germ (W x) (f x.val) (hx x)
      (F.obj.map (homOfLE (hWU x)).op s) =
    F.presheaf.germ (W x) (f x.val) (hx x)
      (g x • F.obj.map (homOfLE (le_top : W x ≤ ⊤)).op σ) at hg
  simp only [map_smul, TopCat.Presheaf.germ_res_apply] at hg
  have hc := congrArg (e x.val).hom hg
  rw [map_smul] at hc
  change openSheafOrientationCoefficient F f e U s x =
    g x * Chern.Sheaf.OrientationCoefficients.sheafOrientationCoefficient F f e σ x.val at hc
  simpa only [hσ, mul_one] using hc

def orientationCoefficientsPresheafIso (hf : Topology.IsClosedEmbedding f)
    (hz : ∀ y, y ∉ Set.range f → IsZero (F.presheaf.stalk y)) :
    F.obj ≅ supportLocallyConstantPresheaf f := by
  let α := orientationCoefficientsPresheafMap F f e σ hσ
  have (U : (Opens X)ᵒᵖ) : IsIso (α.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨openSheafOrientationCoefficients_injective F f e σ hσ hz U.unop,
        openSheafOrientationCoefficients_surjective F f e σ hσ hf hz U.unop⟩
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.SheafOrientationCoefficients
