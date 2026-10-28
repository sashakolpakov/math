import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.DimensionBalance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelOpen

/-! # One Dimension Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.OneDimensionOpen

noncomputable section

/-! The first cohomology dimension of a finite projective complex is
bounded on an explicit open. A fixed finite free cover of degree zero
turns the bound into a sum of two kernel-dimension bounds. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

section Complex

variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{u} R) ℕ)
variable [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]

def cochainOneIncomingFromFree :
    (ULift.{u} (Fin (HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (C.X 0))) → R) →ₗ[R] C.X 1 :=
  (C.d 0 1).hom.comp (HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateEmbedding R (C.X 0)).projection

theorem cochainOne_kernel_dimension_balance [Module.Finite R (C.X 1)]
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K ((cochainOneIncomingFromFree C).baseChange K).ker +
      Module.finrank K ((C.d 1 2).hom.baseChange K).ker =
        Module.finrank K ((ScalarExtensionKernel.cochainScalarExtension C K).homology 1) +
          HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (C.X 0) := by
  let P := HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateEmbedding R (C.X 0)
  have hproj : Function.Surjective (P.projection.baseChange K) := by
    intro x
    exact ⟨(P.baseChange K).inclusion x, (P.baseChange K).projection_inclusion x⟩
  have hcomp : (cochainOneIncomingFromFree C).baseChange K =
      ((C.d 0 1).hom.baseChange K).comp (P.projection.baseChange K) :=
    LinearMap.baseChange_comp P.projection (C.d 0 1).hom
  have hrange : ((cochainOneIncomingFromFree C).baseChange K).range =
      ((C.d 0 1).hom.baseChange K).range := by
    rw [hcomp]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hproj)
  have hfree : Module.finrank K
      (K ⊗[R] (ULift.{u} (Fin (HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (C.X 0))) → R)) =
        HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (C.X 0) := by
    rw [(TensorProduct.piScalarRight R K K
      (ULift.{u} (Fin (HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize R (C.X 0))))).finrank_eq]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_ulift, Fintype.card_fin]
  have hzero := ((cochainOneIncomingFromFree C).baseChange K).finrank_range_add_finrank_ker
  rw [hrange, hfree] at hzero
  have hone := ((C.d 1 2).hom.baseChange K).finrank_range_add_finrank_ker
  let : Module.Finite K ((ScalarExtensionKernel.cochainScalarExtension C K).X 0) :=
    inferInstanceAs (Module.Finite K (K ⊗[R] C.X 0))
  let : Module.Finite K ((ScalarExtensionKernel.cochainScalarExtension C K).X 1) :=
    inferInstanceAs (Module.Finite K (K ⊗[R] C.X 1))
  have hcoh := DimensionBalance.cochain_dimension_balance_succ (ScalarExtensionKernel.cochainScalarExtension C K) 0
  change Module.finrank K (K ⊗[R] C.X 1) =
    Module.finrank K ((ScalarExtensionKernel.cochainScalarExtension C K).homology 1) +
      Module.finrank K ((C.d 0 1).hom.baseChange K).range +
      Module.finrank K ((C.d 1 2).hom.baseChange K).range at hcoh
  omega

end Complex

variable {S : Scheme.{u}} (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
variable [Module.Finite Γ(S, ⊤) (C.X 0)] [Module.Projective Γ(S, ⊤) (C.X 0)]
variable [Module.Finite Γ(S, ⊤) (C.X 1)] [Module.Projective Γ(S, ⊤) (C.X 1)]
variable [Module.Finite Γ(S, ⊤) (C.X 2)] [Module.Projective Γ(S, ⊤) (C.X 2)]

def cochainOneDimensionOpen (d : ℕ) : S.Opens :=
  ⨆ (a : ℕ) (b : ℕ) (_ : a + b ≤ d + HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize Γ(S, ⊤) (C.X 0)),
    HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (cochainOneIncomingFromFree C) a ⊓
      HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (C.d 1 2).hom b

theorem cochainOneDimensionOpen_mem (d : ℕ) (x : S) :
    x ∈ cochainOneDimensionOpen C d ↔
      ∃ a b : ℕ, a + b ≤ d + HilbertConstruction.Finite.ProjectiveKernelMatrix.finiteProjectiveCoordinateSize Γ(S, ⊤) (C.X 0) ∧
        x ∈ HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (cochainOneIncomingFromFree C) a ∧
        x ∈ HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (C.d 1 2).hom b := by
  simp only [cochainOneDimensionOpen, TopologicalSpace.Opens.mem_iSup,
    TopologicalSpace.Opens.mem_inf, exists_prop]

theorem cochainOneDimensionOpen_field_point {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ S) (d : ℕ) :
    (letI := c.appTop.hom.toAlgebra;
      Set.range c ⊆ (cochainOneDimensionOpen C d : Set S) ↔
        Module.finrank Γ(Spec (.of K), ⊤)
          ((ScalarExtensionKernel.cochainScalarExtension C Γ(Spec (.of K), ⊤)).homology 1) ≤ d) := by
  let := c.appTop.hom.toAlgebra
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  have hdim := cochainOne_kernel_dimension_balance C Γ(Spec (.of K), ⊤)
  constructor
  · intro h
    let t : Spec (.of K) := (⊥ : PrimeSpectrum K)
    obtain ⟨a, b, hab, ha, hb⟩ :=
      (cochainOneDimensionOpen_mem C d (c t)).mp (h ⟨t, rfl⟩)
    have ha' : Set.range c ⊆
        (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (cochainOneIncomingFromFree C) a : Set S) := by
      rintro y ⟨s, rfl⟩
      exact (Subsingleton.elim s t) ▸ ha
    have hb' : Set.range c ⊆
        (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (C.d 1 2).hom b : Set S) := by
      rintro y ⟨s, rfl⟩
      exact (Subsingleton.elim s t) ▸ hb
    have hka := (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point
      c (cochainOneIncomingFromFree C) a).mp ha'
    have hkb := (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point c (C.d 1 2).hom b).mp hb'
    omega
  · intro h
    let a := Module.finrank Γ(Spec (.of K), ⊤)
      ((cochainOneIncomingFromFree C).baseChange Γ(Spec (.of K), ⊤)).ker
    let b := Module.finrank Γ(Spec (.of K), ⊤)
      ((C.d 1 2).hom.baseChange Γ(Spec (.of K), ⊤)).ker
    have ha := (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point
      c (cochainOneIncomingFromFree C) a).mpr (le_refl a)
    have hb := (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point
      c (C.d 1 2).hom b).mpr (le_refl b)
    intro x hx
    apply (cochainOneDimensionOpen_mem C d x).mpr
    refine ⟨a, b, ?_, ha hx, hb hx⟩
    dsimp only [a, b]
    omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.OneDimensionOpen
