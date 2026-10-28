/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
This file has been modified.
-/
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! # Resolution Basic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ResolutionBasic

noncomputable section

/- Adapted to HilbertConstruction-local declarations; retain only bundled resolutions and their
augmentation cokernel and positive-degree exactness properties. -/

universe v u v' u'

open _root_.CategoryTheory

open Category Limits _root_.ChainComplex _root_.HomologicalComplex

variable {C : Type u} [Category.{v} C]

open Projective

variable [HasZeroObject C] [HasZeroMorphisms C]

/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.
-/
structure ProjectiveResolution (Z : C) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex C ℕ
  /-- the chain complex must be degreewise projective -/
  projective : ∀ n, Projective (complex.X n) := by infer_instance
  /-- the chain complex must have homology -/
  [hasHomology : ∀ i, complex.HasHomology i]
  /-- the morphism to the single chain complex with `Z` in degree `0` -/
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso π := by infer_instance

open ProjectiveResolution in
attribute [instance] projective hasHomology ProjectiveResolution.quasiIso

namespace ProjectiveResolution

variable {Z : C} (P : ProjectiveResolution Z)

lemma complex_exactAt_succ (n : ℕ) :
    P.complex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)

@[simp]
theorem π_f_succ (n : ℕ) : P.π.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]
theorem complex_d_comp_π_f_zero :
    P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  rw [← P.π.comm 1 0, single_obj_d, comp_zero]

theorem complex_d_succ_comp (n : ℕ) :
    P.complex.d n (n + 1) ≫ P.complex.d (n + 1) (n + 2) = 0 := by
  simp

/-- The (limit) cokernel cofork given by the composition
`P.complex.X 1 ⟶ P.complex.X 0 ⟶ Z` when `P: ProjectiveResolution Z`. -/
@[simp]
noncomputable def cokernelCofork : CokernelCofork (P.complex.d 1 0) :=
  CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

/-- `Z` is the cokernel of `P.complex.X 1 ⟶ P.complex.X 0` when `P: ProjectiveResolution Z`. -/
noncomputable def isColimitCokernelCofork : IsColimit (P.cokernelCofork) := by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  change P.complex.pOpcycles 0 ≫ P.complex.isoHomologyι₀.inv ≫
    homologyMap P.π 0 ≫ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 Z).hom = P.π.f 0
  apply (cancel_mono (singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0 Z).hom).mp
  rw [assoc, assoc, assoc, singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom]
  change P.complex.pOpcycles 0 ≫ P.complex.isoHomologyι₀.inv ≫
      homologyMap P.π 0 ≫ (((ChainComplex.single₀ C).obj Z).isoHomologyι₀).hom = _
  rw [isoHomologyι₀_inv_naturality_assoc, Iso.inv_hom_id, comp_id, p_opcyclesMap]
  have hs : (singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0 Z).hom =
      ((ChainComplex.single₀ C).obj Z).pOpcycles 0 := by
    change (𝟙 Z) ≫ ((ChainComplex.single₀ C).obj Z).pOpcycles 0 = _
    exact id_comp _
  rw [hs]
  rfl

instance (n : ℕ) : Epi (P.π.f n) := by
  cases n with
  | zero => exact epi_of_isColimit_cofork P.isColimitCokernelCofork
  | succ n => exact (isZero_single_obj_X _ _ _ _ (by simp)).epi (P.π.f (n + 1))

end ProjectiveResolution

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ResolutionBasic
