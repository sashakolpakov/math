import Mathlib

/-! # Unit Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.UnitProduct.Disjoint

noncomputable section

/-! A degreewise product decomposition by natural units extends to actual cochain complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} [HasProductsOfShape ι C]
  (F : ι → C ⥤ C) [∀ i, (F i).Additive] (u : ∀ i, 𝟭 C ⟶ F i)

def complexUnitMap (K : CochainComplex C ℤ) (i : ι) :
    K ⟶ ((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K where
  f n := (u i).app (K.X n)
  comm' n m _ := ((u i).naturality (K.d n m)).symm

def complexUnitFanMap (K : CochainComplex C ℤ) :
    K ⟶ ∏ᶜ fun i => ((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  Pi.lift (complexUnitMap F u K)

theorem complexUnitFanMap_eval (K : CochainComplex C ℤ) (n : ℤ) :
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (complexUnitFanMap F u K) ≫
        (PreservesProduct.iso (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
          (fun i => ((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
      Pi.lift (fun i => (u i).app (K.X n)) := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    ← (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_comp]
  change (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (Pi.lift _ ≫ Pi.π _ i) = _
  erw [Pi.lift_comp_π, Pi.lift_comp_π]
  rfl

theorem complexUnitFanMap_isIso (hu : ∀ X : C, IsIso (Pi.lift (fun i => (u i).app X)))
    (K : CochainComplex C ℤ) : IsIso (complexUnitFanMap F u K) := by
  have (n : ℤ) : IsIso ((complexUnitFanMap F u K).f n) := by
    let E := HomologicalComplex.eval C (ComplexShape.up ℤ) n
    let e := PreservesProduct.iso E (fun i => ((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    have h : IsIso (E.map (complexUnitFanMap F u K) ≫ e.hom) := by
      rw [complexUnitFanMap_eval]
      exact hu (K.X n)
    exact (isIso_comp_right_iff (E.map (complexUnitFanMap F u K)) e.hom).mp h
  exact HomologicalComplex.Hom.isIso_of_components (complexUnitFanMap F u K)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.UnitProduct.Disjoint
