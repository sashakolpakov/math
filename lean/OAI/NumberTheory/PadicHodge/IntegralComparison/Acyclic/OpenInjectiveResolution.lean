import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

/-! # Open Injective Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.OpenInjectiveResolution

noncomputable section

/-! The actual augmentation into the chosen injective resolution remains
 a quasi-isomorphism on any open with vanishing positive cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : TopCat.{u}}

def sections (U : Opens X) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

instance sections_additive (U : Opens X) : (sections U).Additive where
  map_add := rfl

instance sections_preservesFiniteLimits (U : Opens X) : PreservesFiniteLimits (sections U) := by
  dsimp only [sections]
  infer_instance

variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : Opens X)

abbrev resolution := injectiveResolution F
abbrev complex := LeftExactResolution.complex (sections U) (resolution F)
abbrev augmentation := LeftExactResolution.augmentation (sections U) (resolution F)

variable (hF : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
  ((AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj F) (q+1)))

include hF in
theorem positive (n : ℕ) : (complex F U).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' (complex F U) n (n+1) (n+2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro x hx
  exact AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections.TopCat.Sheaf.injectiveResolution_sections_exact_succ F U hF n x hx

include hF in
theorem augmentation_quasiIso : QuasiIso (augmentation F U) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨LeftExactResolution.augmentation_exact (sections U) (resolution F), inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans
          ((LeftExactResolution.augmentation_zero (sections U) (resolution F)).symm.trans
            (Category.comp_id _).symm))
        ((Category.id_comp _).trans (Category.comp_id _).symm)
    all_goals first | rfl | exact (complex F U).shape 0 0 (by simp)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt _ (n+1)
      (CochainComplex.exactAt_succ_single_obj _ _)).mpr (positive F U hF n)

include hF in
theorem mapped_quasiIso : QuasiIso
    (((sections U).mapHomologicalComplex (.up ℕ)).map (resolution F).ι) := by
  have he : Single.ComplexTransport.map (sections U) (Iso.refl ((sections U).obj F))
      (resolution F).ι = augmentation F U := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    change (Single.ComplexTransport.map (sections U) (Iso.refl ((sections U).obj F))
      (resolution F).ι).f 0 = (augmentation F U).f 0
    rw [Single.ComplexTransport.map_zero, LeftExactResolution.augmentation_zero]
    exact Category.id_comp _
  have hq := augmentation_quasiIso F U hF
  rw [← he] at hq
  exact quasiIso_of_comp_left
    (Single.ComplexTransport.sourceIso (sections U) (Iso.refl ((sections U).obj F))).inv _
    (hφφ' := hq)

variable {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)

theorem naturality :
    ((sections U).mapHomologicalComplex (.up ℕ)).map (resolution F).ι ≫
      ((sections U).mapHomologicalComplex (.up ℕ)).map
        (InjectiveResolution.desc f (resolution G) (resolution F)) =
    ((sections U).mapHomologicalComplex (.up ℕ)).map ((CochainComplex.single₀ _).map f) ≫
      ((sections U).mapHomologicalComplex (.up ℕ)).map (resolution G).ι := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    InjectiveResolution.desc_commutes]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.OpenInjectiveResolution
