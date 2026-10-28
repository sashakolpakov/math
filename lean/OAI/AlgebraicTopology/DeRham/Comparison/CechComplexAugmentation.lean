import OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation
import Mathlib.Algebra.Homology.QuasiIso

/-! # Cech Complex Augmentation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation

noncomputable section

/-!
# The actual section augmentation and Čech descent square

For a complex of module-valued presheaves, restrict actual sections on W to
an open family contained in W and include them in the zeroth Čech column.
The resulting total augmentation is natural in the given coefficient
cochain map. Its commuting square supplies a precise quasi-isomorphism
descent lemma, without postulating any geometric comparison property.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped BigOperators

universe u

variable {X ι : Type u} [TopologicalSpace X]
variable (U : ι → Opens X) (W : Opens X) (hsub : ∀ i, U i ≤ W)

include hsub in
/-- Every nonempty Čech intersection lies in the containing open domain. -/
theorem cechIntersection_le_openDomain {n : ℕ} (a : Fin (n + 1) → ι) :
    SmoothCech.cechIntersection U a ≤ W := (SmoothCech.cechIntersection_le U a 0).trans (hsub (a 0))

variable (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ)

/-- Restrict one actual section to all intersections of a fixed Čech degree. -/
def cechSectionRestriction (n : ℕ) : F.obj (op W) →ₗ[ℂ] SmoothCech.CechCochain F U n where
  toFun s a := (F.map (homOfLE (cechIntersection_le_openDomain U W hsub a)).op).hom s
  map_add' s t := by
    funext a
    exact map_add _ _ _
  map_smul' z s := by
    funext a
    exact map_smul _ _ _

/-- Further restriction along a tuple map agrees with direct restriction from W. -/
theorem cechSectionRestriction_precomp {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (s : F.obj (op W)) :
    SmoothCech.cechPrecomp F U f (cechSectionRestriction U W hsub F n s) =
      cechSectionRestriction U W hsub F m s := by
  funext a
  change (F.map (homOfLE (SmoothCech.cechIntersection_le_precomp U a f)).op).hom
      ((F.map (homOfLE (cechIntersection_le_openDomain U W hsub (a ∘ f))).op).hom s) =
    (F.map (homOfLE (cechIntersection_le_openDomain U W hsub a)).op).hom s
  exact SmoothCech.cechSection_restrict_trans F _ _ s

/-- The degree-zero section augmentation is actual restriction to the open family. -/
abbrev cechSectionAugmentation : F.obj (op W) →ₗ[ℂ] SmoothCech.CechCochain F U 0 :=
  cechSectionRestriction U W hsub F 0

/-- The actual degree-zero augmentation is killed by the Čech differential. -/
theorem cechSectionAugmentation_delta (s : F.obj (op W)) :
    SmoothCech.cechDelta F U 0 (cechSectionAugmentation U W hsub F s) = 0 := by
  funext a
  rw [SmoothCech.cechDelta_apply]
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
    (SmoothCech.cechPrecomp F U j.succAbove (cechSectionRestriction U W hsub F 0 s)) a) = 0
  simp only [cechSectionRestriction_precomp, Fin.sum_univ_two, Fin.val_zero,
    pow_zero, Fin.val_one, pow_one]
  let t := cechSectionRestriction U W hsub F 1 s a
  change (1 : ℤ) • t + (-1 : ℤ) • t = 0
  exact (congrArg₂ (fun x y : F.obj (op (SmoothCech.cechIntersection U a)) => x + y)
    (one_smul ℤ t) (neg_one_smul ℤ t)).trans (add_neg_cancel t)

variable {F}
variable {G : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ}

/-- Restriction of actual sections is natural in a presheaf morphism. -/
theorem cechSectionRestriction_naturality (α : F ⟶ G) (n : ℕ) (s : F.obj (op W)) :
    SmoothCechDoubleComplex.cechCoefficientMap U α n (cechSectionRestriction U W hsub F n s) =
      cechSectionRestriction U W hsub G n ((α.app (op W)).hom s) := by
  funext a
  exact congrArg (fun f => f.hom s)
    (α.naturality (homOfLE (cechIntersection_le_openDomain U W hsub a)).op)

/-- Evaluation on an actual open domain, as a functor on presheaf complexes. -/
def presheafComplexSectionsFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ ⥤
      CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  (((evaluation ((Opens X)ᵒᵖ) (ModuleCat.{u} ℂ)).obj (op W)).mapHomologicalComplex
    (ComplexShape.up ℕ))

/-- The complex of actual sections on W. -/
abbrev presheafComplexSections
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ) :=
  (presheafComplexSectionsFunctor W).obj K

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ)

@[simp]
theorem presheafComplexSections_X (q : ℕ) :
    (presheafComplexSections W K).X q = (K.X q).obj (op W) := rfl

@[simp]
theorem presheafComplexSections_d (q r : ℕ) :
    (presheafComplexSections W K).d q r = (K.d q r).app (op W) := rfl

/-- The actual section complex augments the zeroth Čech column. -/
def cechColumnAugmentation : presheafComplexSections W K ⟶ (CechDoubleComplexFunctor.cechDoubleComplex U K).X 0 :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom (cechSectionAugmentation U W hsub (K.X q)))
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact cechSectionRestriction_naturality U W hsub (K.d q (q + 1)) 0 s)

@[simp]
theorem cechColumnAugmentation_f (q : ℕ) :
    (cechColumnAugmentation U W hsub K).f q =
      ModuleCat.ofHom (cechSectionAugmentation U W hsub (K.X q)) := rfl

/-- The actual section augmentation is annihilated by the first horizontal differential. -/
theorem cechColumnAugmentation_horizontal :
    cechColumnAugmentation U W hsub K ≫ (CechDoubleComplexFunctor.cechDoubleComplex U K).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  change ModuleCat.ofHom (cechSectionAugmentation U W hsub (K.X q)) ≫
    ((CechDoubleComplexFunctor.cechDoubleComplex U K).d 0 1).f q = 0
  rw [CechDoubleComplexFunctor.cechDoubleComplex_d_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact cechSectionAugmentation_delta U W hsub (K.X q) s

/-- The generic total augmentation is the actual section restriction map. -/
def cechTotalAugmentation : presheafComplexSections W K ⟶ CechTotalFunctor.cechTotalComplex U K :=
  DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (CechDoubleComplexFunctor.cechDoubleComplex U K)
    (cechColumnAugmentation U W hsub K) (cechColumnAugmentation_horizontal U W hsub K)

@[simp]
theorem cechTotalAugmentation_f (q : ℕ) :
    (cechTotalAugmentation U W hsub K).f q =
      (cechColumnAugmentation U W hsub K).f q ≫
        CechTotalFunctor.cechTotalInclusion U K 0 q q (Nat.zero_add q) := rfl

variable {K}
variable {L : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ}

/-- Evaluation of the given coefficient cochain map on the actual open domain. -/
abbrev presheafComplexSectionsMap (φ : K ⟶ L) :
    presheafComplexSections W K ⟶ presheafComplexSections W L :=
  (presheafComplexSectionsFunctor W).map φ

@[simp]
theorem presheafComplexSectionsMap_f (φ : K ⟶ L) (q : ℕ) :
    (presheafComplexSectionsMap W φ).f q = (φ.f q).app (op W) := rfl

/-- Naturality of the actual column augmentation under coefficient cochain maps. -/
theorem cechColumnAugmentation_naturality (φ : K ⟶ L) :
    presheafComplexSectionsMap W φ ≫ cechColumnAugmentation U W hsub L =
      cechColumnAugmentation U W hsub K ≫ (CechDoubleComplexFunctor.cechDoubleComplexMap U φ).f 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact (cechSectionRestriction_naturality U W hsub (φ.f q) 0 s).symm

/-- The Čech descent square commutes for the actual coefficient cochain map. -/
theorem cechTotalAugmentation_naturality (φ : K ⟶ L) :
    presheafComplexSectionsMap W φ ≫ cechTotalAugmentation U W hsub L =
      cechTotalAugmentation U W hsub K ≫ CechTotalFunctor.cechTotalMap U φ := by
  apply HomologicalComplex.Hom.ext
  funext q
  let f := (presheafComplexSectionsMap W φ).f q
  let aK := (cechColumnAugmentation U W hsub K).f q
  let aL := (cechColumnAugmentation U W hsub L).f q
  let b := ((CechDoubleComplexFunctor.cechDoubleComplexMap U φ).f 0).f q
  let iK := CechTotalFunctor.cechTotalInclusion U K 0 q q (Nat.zero_add q)
  let iL := CechTotalFunctor.cechTotalInclusion U L 0 q q (Nat.zero_add q)
  let t := (CechTotalFunctor.cechTotalMap U φ).f q
  have hc : f ≫ aL = aK ≫ b := congrArg (fun a => a.f q)
    (cechColumnAugmentation_naturality U W hsub φ)
  have hi : iK ≫ t = b ≫ iL :=
    CechTotalFunctor.cechTotalInclusion_map U φ 0 q q (Nat.zero_add q)
  change f ≫ (aL ≫ iL) = (aK ≫ iK) ≫ t
  calc
    f ≫ (aL ≫ iL) = (f ≫ aL) ≫ iL := (Category.assoc _ _ _).symm
    _ = (aK ≫ b) ≫ iL := congrArg (fun a => a ≫ iL) hc
    _ = aK ≫ (b ≫ iL) := Category.assoc _ _ _
    _ = aK ≫ (iK ≫ t) := congrArg (fun a => aK ≫ a) hi.symm
    _ = (aK ≫ iK) ≫ t := (Category.assoc _ _ _).symm

/-- If both actual augmentations and the actual total map are quasi-isomorphisms,
the given coefficient map evaluated on W is a quasi-isomorphism. -/
theorem cechTotalAugmentation_quasiIso_descent (φ : K ⟶ L)
    (hK : QuasiIso (cechTotalAugmentation U W hsub K))
    (hL : QuasiIso (cechTotalAugmentation U W hsub L))
    (hT : QuasiIso (CechTotalFunctor.cechTotalMap U φ)) :
    QuasiIso (presheafComplexSectionsMap W φ) := by
  let : QuasiIso (cechTotalAugmentation U W hsub K) := hK
  let : QuasiIso (cechTotalAugmentation U W hsub L) := hL
  let : QuasiIso (CechTotalFunctor.cechTotalMap U φ) := hT
  let : QuasiIso (presheafComplexSectionsMap W φ ≫ cechTotalAugmentation U W hsub L) := by
    rw [cechTotalAugmentation_naturality]
    infer_instance
  exact quasiIso_of_comp_right (presheafComplexSectionsMap W φ)
    (cechTotalAugmentation U W hsub L)

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
