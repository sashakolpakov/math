import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.LinearAlgebra.Basis.Prod
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.KoszulComplex
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Finite Terms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.FiniteTerms

noncomputable section

/-! The actual scalar Koszul terms are finite free when the coefficient module is finite free, and the final degree-zero term identifies with that coefficient module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R]

def scalarKoszulConsTermIso (M : ModuleCat.{u} R) (r : R) (rs : List R) (i : ℤ) :
    (KoszulComplex.scalarKoszulComplex M (r :: rs)).X i ≅
      ModuleCat.of R ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1) × (KoszulComplex.scalarKoszulComplex M rs).X i) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)) i (i + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _

theorem scalarKoszulComplex_finite_free (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Free R M] (rs : List R) :
    ∀ i, Module.Finite R ((KoszulComplex.scalarKoszulComplex M rs).X i) ∧
      Module.Free R ((KoszulComplex.scalarKoszulComplex M rs).X i) := by
  induction rs with
  | nil =>
    intro i
    by_cases hi : i = 0
    · subst i
      let e := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm.toLinearEquiv
      exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
    · have : Subsingleton ((KoszulComplex.scalarKoszulComplex M []).X i) :=
        ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
      exact ⟨inferInstance, inferInstance⟩
  | cons r rs ih =>
    intro i
    have : Module.Finite R ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1)) := (ih (i + 1)).1
    have : Module.Free R ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1)) := (ih (i + 1)).2
    have : Module.Finite R ((KoszulComplex.scalarKoszulComplex M rs).X i) := (ih i).1
    have : Module.Free R ((KoszulComplex.scalarKoszulComplex M rs).X i) := (ih i).2
    let e : ((KoszulComplex.scalarKoszulComplex M rs).X (i + 1) × (KoszulComplex.scalarKoszulComplex M rs).X i) ≃ₗ[R]
        (KoszulComplex.scalarKoszulComplex M (r :: rs)).X i :=
      (scalarKoszulConsTermIso M r rs i).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩

def mappingConeSndIsoOfZeroNext (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : C ⟶ C) (i : ℤ) (hz : IsZero (C.X (i + 1))) :
    (CochainComplex.mappingCone f).X i ≅ C.X i where
  hom := (CochainComplex.mappingCone.snd f).v i i (add_zero i)
  inv := (CochainComplex.mappingCone.inr f).f i
  hom_inv_id := by
    have hf : (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl = 0 := hz.eq_of_tgt _ _
    have h := CochainComplex.mappingCone.id_X f i (i + 1) rfl
    rw [hf, zero_comp, zero_add] at h
    exact h
  inv_hom_id := CochainComplex.mappingCone.inr_f_snd_v f i

def scalarKoszulZeroTermIso (M : ModuleCat.{u} R) :
    ∀ rs : List R, (KoszulComplex.scalarKoszulComplex M rs).X 0 ≅ M
  | [] => HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  | r :: rs => by
    exact mappingConeSndIsoOfZeroNext (KoszulComplex.scalarKoszulComplex M rs)
      (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)) 0
        (KoszulComplex.scalarKoszulComplex_isZero_X M rs 1 (Or.inr (by decide))) ≪≫
      scalarKoszulZeroTermIso M rs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.FiniteTerms
