import OAI.AlgebraicGeometry.Comparison.Betti.RegularFunctions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Affine Iso Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation

noncomputable section

section

/-!
# Regular-function realization on actual Zariski opens

The scalar-compatible identification of sections with global sections of an
open subscheme gives analytic evaluation on every open. Its restriction law
is proved from the structure sheaf and the actual open-immersion point maps.
No smoothness, irreducibility, or properness hypothesis is needed here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev openOver (U : X.left.Opens) : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (U.ι ≫ X.hom)

abbrev openInclusion (U : X.left.Opens) : openOver X U ⟶ X := Over.homMk U.ι rfl

instance openInclusion_isOpenImmersion (U : X.left.Opens) :
    IsOpenImmersion (openInclusion X U).left := by
  change IsOpenImmersion U.ι
  infer_instance

abbrev openRestriction {V U : X.left.Opens} (h : V ≤ U) : openOver X V ⟶ openOver X U :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (U.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem openRestriction_inclusion {V U : X.left.Opens} (h : V ≤ U) :
    openRestriction X h ≫ openInclusion X U = openInclusion X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

theorem openTopIso_appLE (U : X.left.Opens) :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/-- The usual open-section identification respects the actual complex scalars. -/
def openSectionTopAlgHom (U : X.left.Opens) :
    Γ(X.left, U) →ₐ[ℂ] Γ((openOver X U).left, ⊤) where
  __ := U.topIso.inv.hom
  commutes' c := by
    have h := Scheme.Hom.appLE_comp_appLE U.ι X.hom ⊤ U ⊤ le_top U.ι_preimage_self.ge
    rw [openTopIso_appLE] at h
    exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of ℂ)).inv c)

theorem openTopIso_inv_restrict {V U : X.left.Opens} (h : V ≤ U) :
    X.left.presheaf.map (homOfLE h).op ≫ V.topIso.inv =
      U.topIso.inv ≫ (X.left.homOfLE h).appTop := by
  have heq : (homOfLE h).op ≫ (eqToHom V.ι_image_top).op =
      (eqToHom U.ι_image_top).op ≫
        (homOfLE (X.left.ι_image_homOfLE_le_ι_image h ⊤)).op := Subsingleton.elim _ _
  have hright := congrArg (fun g : Γ(U.toScheme, ⊤) ⟶ Γ(V.toScheme, ⊤) => U.topIso.inv ≫ g)
    (X.left.homOfLE_appTop h)
  exact (X.left.presheaf.map_comp (homOfLE h).op (eqToHom V.ι_image_top).op).symm.trans
    ((congrArg X.left.presheaf.map heq).trans
      ((X.left.presheaf.map_comp (eqToHom U.ι_image_top).op
        (homOfLE (X.left.ι_image_homOfLE_le_ι_image h ⊤)).op).trans hright.symm))

/-- Analytic realization of a section as a function on the open subscheme. -/
def openSectionAnalyticAlgHom (U : X.left.Opens) :
    Γ(X.left, U) →ₐ[ℂ] RegularFunctions.regularAnalyticFunctions (openOver X U) :=
  (RegularFunctions.globalSectionAnalyticAlgHom (openOver X U)).comp (openSectionTopAlgHom X U)

theorem openSectionAnalyticAlgHom_restrict {V U : X.left.Opens} (h : V ≤ U) :
    (openSectionAnalyticAlgHom X V).comp (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) =
      (RegularFunctions.analyticFunctionPullback (openRestriction X h)).comp (openSectionAnalyticAlgHom X U) := by
  ext s p
  change RegularFunctions.globalEvaluation p (V.topIso.inv (X.left.presheaf.map (homOfLE h).op s)) =
    RegularFunctions.globalEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) p) (U.topIso.inv s)
  rw [RegularFunctions.globalEvaluation_map]
  exact congrArg (RegularFunctions.globalEvaluation p) (ConcreteCategory.congr_hom (openTopIso_inv_restrict X h) s)

def analyticOpen (U : X.left.Opens) : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.left),
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpen_preimage_underlying _ U.isOpen⟩

/-- Native points of the open subscheme are its actual analytic open subset. -/
def openPointHomeomorph (U : X.left.Opens) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X U) ≃ₜ analyticOpen X U :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph (openInclusion X U)).trans
    (Homeomorph.setCongr (by
      change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X)) ⁻¹' Set.range U.ι =
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X)) ⁻¹' (U : Set X.left)
      rw [Scheme.Opens.range_ι]))

@[simp]
theorem openPointHomeomorph_val (U : X.left.Opens)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X U)) :
    (openPointHomeomorph X U p).val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openInclusion X U) p := rfl

theorem openPointHomeomorph_restrict {V U : X.left.Opens} (h : V ≤ U)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X V)) :
    openPointHomeomorph X U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) p) =
      ⟨(openPointHomeomorph X V p).val, h (openPointHomeomorph X V p).property⟩ := by
  apply Subtype.ext
  simp only [openPointHomeomorph_val, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, openRestriction_inclusion]

/-- The evaluated function on the corresponding open subset of complex points. -/
def sectionEvaluationOn (U : X.left.Opens) : Γ(X.left, U) →ₐ[ℂ] C(analyticOpen X U, ℂ) where
  toFun s := ((openSectionAnalyticAlgHom X U s).val).comp
    ⟨(openPointHomeomorph X U).symm, (openPointHomeomorph X U).symm.continuous⟩
  map_zero' := by ext p; exact congrArg (fun g : RegularFunctions.regularAnalyticFunctions (openOver X U) =>
      g.val ((openPointHomeomorph X U).symm p)) (map_zero (openSectionAnalyticAlgHom X U))
  map_one' := by ext p; exact congrArg (fun g : RegularFunctions.regularAnalyticFunctions (openOver X U) =>
      g.val ((openPointHomeomorph X U).symm p)) (map_one (openSectionAnalyticAlgHom X U))
  map_add' s t := by ext p; exact congrArg (fun g : RegularFunctions.regularAnalyticFunctions (openOver X U) =>
      g.val ((openPointHomeomorph X U).symm p)) (map_add (openSectionAnalyticAlgHom X U) s t)
  map_mul' s t := by ext p; exact congrArg (fun g : RegularFunctions.regularAnalyticFunctions (openOver X U) =>
      g.val ((openPointHomeomorph X U).symm p)) (map_mul (openSectionAnalyticAlgHom X U) s t)
  commutes' c := by ext p; exact congrArg (fun g : RegularFunctions.regularAnalyticFunctions (openOver X U) =>
      g.val ((openPointHomeomorph X U).symm p)) ((openSectionAnalyticAlgHom X U).commutes c)

/-- Evaluation commutes with the literal restriction of functions to smaller opens. -/
theorem sectionEvaluationOn_restrict {V U : X.left.Opens} (h : V ≤ U)
    (s : Γ(X.left, U)) (p : analyticOpen X V) :
    sectionEvaluationOn X V (X.left.presheaf.map (homOfLE h).op s) p =
      sectionEvaluationOn X U s ⟨p.val, h p.property⟩ := by
  have hp : (openPointHomeomorph X U).symm ⟨p.val, h p.property⟩ =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) ((openPointHomeomorph X V).symm p) := by
    apply (openPointHomeomorph X U).injective
    rw [Homeomorph.apply_symm_apply, openPointHomeomorph_restrict, Homeomorph.apply_symm_apply]
  change RegularFunctions.globalEvaluation ((openPointHomeomorph X V).symm p)
      (V.topIso.inv (X.left.presheaf.map (homOfLE h).op s)) =
    RegularFunctions.globalEvaluation ((openPointHomeomorph X U).symm ⟨p.val, h p.property⟩) (U.topIso.inv s)
  rw [hp, RegularFunctions.globalEvaluation_map]
  exact congrArg (RegularFunctions.globalEvaluation ((openPointHomeomorph X V).symm p))
    (ConcreteCategory.congr_hom (openTopIso_inv_restrict X h) s)

end

/-! Evaluation in a specified affine coordinate isomorphism uses its original
map on regular sections. This applies to the native projective charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
  (A : CommAlgCat.{0} ℂ) (e : openOver X U ≅ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)

def affineIsoPointInOpen (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : analyticOpen X U :=
  openPointHomeomorph X U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.inv (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A p))

theorem sectionEvaluationOn_affineIso (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (s : Γ(X.left, U)) :
    sectionEvaluationOn X U s (affineIsoPointInOpen X U A e p) =
      p ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (e.inv.left.appTop (U.topIso.inv s))) := by
  change RegularFunctions.globalEvaluation ((openPointHomeomorph X U).symm
      (openPointHomeomorph X U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.inv (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A p))))
        (U.topIso.inv s) = _
  rw [Homeomorph.symm_apply_apply, RegularFunctions.globalEvaluation_map, RegularFunctions.globalEvaluation_affine]

theorem affineIsoPointInOpen_val (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    (affineIsoPointInOpen X U A e p).val =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (e.inv ≫ openInclusion X U) p := by
  rw [affineIsoPointInOpen, openPointHomeomorph_val, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
