import OAI.Analysis.DifferentialForms.Manifold.OpenD
import OAI.Analysis.DifferentialForms.Manifold.DeRham

/-! # Open De Rham X -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# De Rham complexes on open domains and their restrictions

The objects are genuine smooth forms on open subsets of a real normed space.
Restriction commutes with the constructed exterior derivative and therefore
induces cochain maps and cohomology maps. The resulting cohomology assignment
is a presheaf; no sheaf property or local exactness is asserted here.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U V W : Opens E}

/-- The complex of actual smooth forms on an open domain. -/
def OpenDeRhamX.openDeRhamComplex (U : Opens E) : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (OpenD.SmoothOpenForm U n))
    (fun _ => ModuleCat.ofHom OpenD.SmoothOpenForm.d)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext OpenD.SmoothOpenForm.d_squared))

@[simp]
theorem OpenDeRhamX.openDeRhamComplex_X (U : Opens E) (n : ℕ) :
    (OpenDeRhamX.openDeRhamComplex U).X n = ModuleCat.of ℂ (OpenD.SmoothOpenForm U n) := rfl

@[simp]
theorem OpenDeRhamX.openDeRhamComplex_d (U : Opens E) (n : ℕ) :
    (OpenDeRhamX.openDeRhamComplex U).d n (n + 1) = ModuleCat.ofHom
      (OpenD.SmoothOpenForm.d : OpenD.SmoothOpenForm U n →ₗ[ℂ] OpenD.SmoothOpenForm U (n + 1)) := by
  exact CochainComplex.of_d
    (fun k => ModuleCat.of ℂ (OpenD.SmoothOpenForm U k))
    (fun k => ModuleCat.ofHom (OpenD.SmoothOpenForm.d :
      OpenD.SmoothOpenForm U k →ₗ[ℂ] OpenD.SmoothOpenForm U (k + 1))) n

/-- Restriction to a smaller open set is a cochain map. -/
def OpenDeRhamX.openDeRhamRestrict (h : V ≤ U) : OpenDeRhamX.openDeRhamComplex U ⟶ OpenDeRhamX.openDeRhamComplex V :=
  CochainComplex.ofHom
    (fun _ => ModuleCat.ofHom (OpenD.SmoothOpenForm.restrict h))
    (fun n => by
      rw [OpenDeRhamX.openDeRhamComplex_d, OpenDeRhamX.openDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact (OpenD.SmoothOpenForm.restrict_d h form).symm)

@[simp]
theorem OpenDeRhamX.openDeRhamRestrict_f_apply (h : V ≤ U) (n : ℕ) (form : OpenD.SmoothOpenForm U n) :
    (OpenDeRhamX.openDeRhamRestrict h).f n form = OpenD.SmoothOpenForm.restrict h form := rfl

@[simp]
theorem OpenDeRhamX.openDeRhamRestrict_refl (U : Opens E) :
    OpenDeRhamX.openDeRhamRestrict (le_refl U) = 𝟙 (OpenDeRhamX.openDeRhamComplex U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact OpenD.SmoothOpenForm.restrict_refl form

theorem OpenDeRhamX.openDeRhamRestrict_comp (hVU : V ≤ U) (hWV : W ≤ V) :
    OpenDeRhamX.openDeRhamRestrict (hWV.trans hVU) =
      OpenDeRhamX.openDeRhamRestrict hVU ≫ OpenDeRhamX.openDeRhamRestrict hWV := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact (OpenD.SmoothOpenForm.restrict_trans hVU hWV form).symm

/-- Actual de Rham cohomology on the open domain. -/
def OpenDeRhamX.openDeRhamCohomology (U : Opens E) (n : ℕ) : ModuleCat.{u} ℂ :=
  (OpenDeRhamX.openDeRhamComplex U).homology n

/-- Restriction on open-domain de Rham cohomology. -/
def OpenDeRhamX.openDeRhamCohomologyRestrict (h : V ≤ U) (n : ℕ) :
    OpenDeRhamX.openDeRhamCohomology U n ⟶ OpenDeRhamX.openDeRhamCohomology V n :=
  HomologicalComplex.homologyMap (OpenDeRhamX.openDeRhamRestrict h) n

@[simp]
theorem OpenDeRhamX.openDeRhamCohomologyRestrict_refl (U : Opens E) (n : ℕ) :
    OpenDeRhamX.openDeRhamCohomologyRestrict (le_refl U) n = 𝟙 (OpenDeRhamX.openDeRhamCohomology U n) := by
  change HomologicalComplex.homologyMap (OpenDeRhamX.openDeRhamRestrict (le_refl U)) n =
    𝟙 ((OpenDeRhamX.openDeRhamComplex U).homology n)
  rw [OpenDeRhamX.openDeRhamRestrict_refl, HomologicalComplex.homologyMap_id]

theorem OpenDeRhamX.openDeRhamCohomologyRestrict_comp (hVU : V ≤ U) (hWV : W ≤ V) (n : ℕ) :
    OpenDeRhamX.openDeRhamCohomologyRestrict (hWV.trans hVU) n =
      OpenDeRhamX.openDeRhamCohomologyRestrict hVU n ≫ OpenDeRhamX.openDeRhamCohomologyRestrict hWV n := by
  change HomologicalComplex.homologyMap (OpenDeRhamX.openDeRhamRestrict (hWV.trans hVU)) n =
    HomologicalComplex.homologyMap (OpenDeRhamX.openDeRhamRestrict hVU) n ≫
      HomologicalComplex.homologyMap (OpenDeRhamX.openDeRhamRestrict hWV) n
  rw [OpenDeRhamX.openDeRhamRestrict_comp, HomologicalComplex.homologyMap_comp]

variable (E) in
/-- The presheaf of de Rham cochain complexes on the open subsets of E. -/
def OpenDeRhamX.openDeRhamPresheaf : (Opens E)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} ℂ) ℕ where
  obj U := OpenDeRhamX.openDeRhamComplex (unop U)
  map f := OpenDeRhamX.openDeRhamRestrict (leOfHom f.unop)
  map_id U := OpenDeRhamX.openDeRhamRestrict_refl (unop U)
  map_comp f g := OpenDeRhamX.openDeRhamRestrict_comp (leOfHom f.unop) (leOfHom g.unop)

variable (E) in
/-- The presheaf obtained by taking degree-n de Rham cohomology. -/
def OpenDeRhamX.openDeRhamCohomologyPresheaf (n : ℕ) : (Opens E)ᵒᵖ ⥤ ModuleCat.{u} ℂ :=
  OpenDeRhamX.openDeRhamPresheaf E ⋙ HomologicalComplex.homologyFunctor _ _ n

section

/-- Restricting a global smooth form commutes with exterior differentiation. -/
theorem Basic.SmoothForm.onOpen_d (U : Opens E) {n : ℕ} (form : Basic.SmoothForm E n) :
    OpenD.SmoothOpenForm.d (Basic.SmoothForm.onOpen U form) = Basic.SmoothForm.onOpen U (Basic.SmoothForm.d form) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  exact OpenD.SmoothOpenForm.d_ofRaw_apply (form : Basic.RawForm E n) form.smooth.contDiffOn x

end

/-- Restricting global smooth forms to an open set gives a cochain map. -/
def OpenDeRhamX.deRhamOnOpen (U : Opens E) : DeRham.deRhamComplex E ⟶ OpenDeRhamX.openDeRhamComplex U :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (Basic.SmoothForm.onOpen U))
    (fun n => by
      rw [DeRham.deRhamComplex_d, OpenDeRhamX.openDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact Basic.SmoothForm.onOpen_d U form)

theorem OpenDeRhamX.deRhamOnOpen_restrict (h : V ≤ U) :
    OpenDeRhamX.deRhamOnOpen U ≫ OpenDeRhamX.openDeRhamRestrict h = OpenDeRhamX.deRhamOnOpen V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Basic.SmoothForm.restrict_onOpen h form

/-- Restriction of global de Rham cohomology to an open set. -/
def OpenDeRhamX.deRhamCohomologyOnOpen (U : Opens E) (n : ℕ) :
    DeRham.deRhamCohomology E n ⟶ OpenDeRhamX.openDeRhamCohomology U n :=
  HomologicalComplex.homologyMap (OpenDeRhamX.deRhamOnOpen U) n

theorem OpenDeRhamX.deRhamCohomologyOnOpen_restrict (h : V ≤ U) (n : ℕ) :
    OpenDeRhamX.deRhamCohomologyOnOpen U n ≫ OpenDeRhamX.openDeRhamCohomologyRestrict h n =
      OpenDeRhamX.deRhamCohomologyOnOpen V n := by
  change HomologicalComplex.homologyMap (OpenDeRhamX.deRhamOnOpen U) n ≫
    HomologicalComplex.homologyMap (OpenDeRhamX.openDeRhamRestrict h) n =
      HomologicalComplex.homologyMap (OpenDeRhamX.deRhamOnOpen V) n
  rw [← HomologicalComplex.homologyMap_comp, OpenDeRhamX.deRhamOnOpen_restrict]

end

end OAI.Analysis.DifferentialForms.Manifold
