import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechAugmentation
import Mathlib.Algebra.Homology.TotalComplex

/-! # Smooth Cech Double Complex -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex

noncomputable section

/-!
# The actual smooth Čech–de Rham bicomplex

At horizontal degree n and vertical degree p the object consists of smooth
p-forms on all (n+1)-fold intersections. The horizontal differential is the
signed Čech restriction map and the vertical differential is the actual
exterior derivative. Their commutation follows from naturality of restriction.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped Simplicial

universe u

section Coefficients

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)
variable {F G : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ} (α : F ⟶ G)

/-- A morphism of actual presheaves acts on each Čech section. -/
def cechCoefficientMap (n : ℕ) :
    SmoothCech.CechCochain F U n →ₗ[ℂ] SmoothCech.CechCochain G U n where
  toFun c a := (α.app (op (SmoothCech.cechIntersection U a))).hom (c a)
  map_add' c d := by
    funext a
    exact map_add _ _ _
  map_smul' z c := by
    funext a
    exact map_smul _ _ _

/-- Coefficient maps are natural for every Čech cosimplicial operator. -/
def cechCoefficientNat : SmoothCech.cechCosimplicial F U ⟶ SmoothCech.cechCosimplicial G U where
  app n := ModuleCat.ofHom (cechCoefficientMap U α n.len)
  naturality n m f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext a
    change (α.app (op (SmoothCech.cechIntersection U a))).hom
      ((F.map (homOfLE (SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op).hom
        (c (a ∘ f.toOrderHom))) =
      (G.map (homOfLE (SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op).hom
        ((α.app (op (SmoothCech.cechIntersection U (a ∘ f.toOrderHom)))).hom
          (c (a ∘ f.toOrderHom)))
    exact congrArg (fun k => k.hom (c (a ∘ f.toOrderHom)))
      (α.naturality (homOfLE (SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)).op)

/-- A presheaf morphism induces the ordinary coefficient map of Čech complexes. -/
def cechCoefficientHom : SmoothCech.cechComplex F U ⟶ SmoothCech.cechComplex G U :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (cechCoefficientNat U α)

@[simp]
theorem cechCoefficientHom_f (n : ℕ) :
    (cechCoefficientHom U α).f n = ModuleCat.ofHom (cechCoefficientMap U α n) := rfl

/-- Acting on coefficients commutes with the signed Čech differential. -/
theorem cechCoefficientMap_delta (n : ℕ) (c : SmoothCech.CechCochain F U n) :
    cechCoefficientMap U α (n + 1) (SmoothCech.cechDelta F U n c) =
      SmoothCech.cechDelta G U n (cechCoefficientMap U α n c) := by
  have h := (cechCoefficientHom U α).comm n (n + 1)
  rw [SmoothCech.cechComplex_d, SmoothCech.cechComplex_d, cechCoefficientHom_f, cechCoefficientHom_f] at h
  exact (congrArg (fun k => k.hom c) h).symm

end Coefficients

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → Opens E)

/-- Exterior differentiation acts on each actual section of a Čech cochain. -/
abbrev smoothCechExteriorD (p n : ℕ) :
    SmoothCech.SmoothCechCochain U p n →ₗ[ℂ] SmoothCech.SmoothCechCochain U (p + 1) n :=
  cechCoefficientMap U (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheafD E p) n

@[simp]
theorem smoothCechExteriorD_apply (p n : ℕ) (c : SmoothCech.SmoothCechCochain U p n)
    (a : Fin (n + 1) → ι) :
    smoothCechExteriorD U p n c a = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (c a) := rfl

/-- The vertical differential squares to zero on the genuine form sections. -/
theorem smoothCechExteriorD_squared (p n : ℕ) (c : SmoothCech.SmoothCechCochain U p n) :
    smoothCechExteriorD U (p + 1) n (smoothCechExteriorD U p n c) = 0 := by
  funext a
  exact Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_squared (c a)

/-- Naturality of exterior differentiation proves commutation with the Čech differential. -/
theorem smoothCechExteriorD_delta (p n : ℕ) (c : SmoothCech.SmoothCechCochain U p n) :
    smoothCechExteriorD U p (n + 1) (SmoothCech.smoothCechDelta U p n c) =
      SmoothCech.smoothCechDelta U (p + 1) n (smoothCechExteriorD U p n c) :=
  cechCoefficientMap_delta U (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheafD E p) n c

/-- A column is the actual de Rham complex of forms on the indicated intersections. -/
def smoothCechColumn (n : ℕ) : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of ℂ (SmoothCech.SmoothCechCochain U p n))
    (fun p => ModuleCat.ofHom (smoothCechExteriorD U p n))
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact smoothCechExteriorD_squared U p n c)

@[simp]
theorem smoothCechColumn_X (n p : ℕ) :
    (smoothCechColumn U n).X p = ModuleCat.of ℂ (SmoothCech.SmoothCechCochain U p n) := rfl

@[simp]
theorem smoothCechColumn_d (n p : ℕ) :
    (smoothCechColumn U n).d p (p + 1) = ModuleCat.ofHom (smoothCechExteriorD U p n) :=
  CochainComplex.of_d (fun q => ModuleCat.of ℂ (SmoothCech.SmoothCechCochain U q n))
    (fun q => ModuleCat.ofHom (smoothCechExteriorD U q n)) p

/-- The actual Čech differential is a cochain map between de Rham columns. -/
def smoothCechHorizontal (n : ℕ) : smoothCechColumn U n ⟶ smoothCechColumn U (n + 1) :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (SmoothCech.smoothCechDelta U p n))
    (fun p => by
      rw [smoothCechColumn_d, smoothCechColumn_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact smoothCechExteriorD_delta U p n c)

@[simp]
theorem smoothCechHorizontal_f (n p : ℕ) :
    (smoothCechHorizontal U n).f p = ModuleCat.ofHom (SmoothCech.smoothCechDelta U p n) := rfl

theorem smoothCechHorizontal_squared (n : ℕ) :
    smoothCechHorizontal U n ≫ smoothCechHorizontal U (n + 1) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact SmoothCech.smoothCechDelta_squared U p n c

/-- The genuine smooth Čech–de Rham bicomplex, with Čech degree first. -/
def smoothCechDoubleComplex :
    HomologicalComplex₂ (ModuleCat.{u} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CochainComplex.of (smoothCechColumn U) (smoothCechHorizontal U)
    (smoothCechHorizontal_squared U)

@[simp]
theorem smoothCechDoubleComplex_XX (n p : ℕ) :
    ((smoothCechDoubleComplex U).X n).X p =
      ModuleCat.of ℂ (SmoothCech.SmoothCechCochain U p n) := rfl

@[simp]
theorem smoothCechDoubleComplex_d_f (n p : ℕ) :
    ((smoothCechDoubleComplex U).d n (n + 1)).f p =
      ModuleCat.ofHom (SmoothCech.smoothCechDelta U p n) :=
  congrArg (fun f => f.f p)
    (CochainComplex.of_d (smoothCechColumn U) (smoothCechHorizontal U) n)

@[simp]
theorem smoothCechDoubleComplex_X_d (n p : ℕ) :
    ((smoothCechDoubleComplex U).X n).d p (p + 1) =
      ModuleCat.ofHom (smoothCechExteriorD U p n) := smoothCechColumn_d U n p

/-- The rows recover exactly the previously constructed signed Čech complexes. -/
theorem smoothCechDoubleComplex_row (p : ℕ) :
    (smoothCechDoubleComplex U).flip.X p = SmoothCech.smoothCechComplex U p := by
  refine HomologicalComplex.ext rfl ?_
  intro i j hij
  obtain rfl := (show i + 1 = j from hij)
  change ((smoothCechDoubleComplex U).d i (i + 1)).f p = _
  rw [smoothCechDoubleComplex_d_f, SmoothCech.cechComplex_d]
  rfl

variable (W : Opens E) (hsub : ∀ i, U i ≤ W)

/-- Restriction of open-domain forms gives the actual de Rham augmentation of column zero. -/
def smoothCechColumnAugmentation : Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex W ⟶ smoothCechColumn U 0 :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (SmoothCechAugmentation.smoothCechAugmentation U p W hsub))
    (fun p => by
      rw [smoothCechColumn_d, Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      funext a
      exact (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_d
        ((SmoothCech.cechIntersection_le U a 0).trans (hsub (a 0))) form).symm)

@[simp]
theorem smoothCechColumnAugmentation_f (p : ℕ) :
    (smoothCechColumnAugmentation U W hsub).f p =
      ModuleCat.ofHom (SmoothCechAugmentation.smoothCechAugmentation U p W hsub) := rfl

/-- The genuine augmentation is annihilated by the first horizontal differential. -/
theorem smoothCechColumnAugmentation_horizontal :
    smoothCechColumnAugmentation U W hsub ≫ smoothCechHorizontal U 0 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact SmoothCechAugmentation.smoothCechDelta_augmentation U p W hsub form

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex
