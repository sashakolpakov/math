import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese

/-! # Albanese Transfer -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Transport the ordinary Albanese universal property along the actual
source and group-scheme isomorphisms of a complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem Components.ComponentAlbaneseData.isComplexAlbanese_of_fiber_iso
    {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eX : D.complexSurface c j ≅ X.toOver)
    (eA : (D.complexAbelian c j).X ≅ A.toOver) [IsMonHom eA.hom]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (a : X.toOver ⟶ A.toOver)
    (hpoint : D.complexBasePoint c j ≫ eX.hom = x₀)
    (hcompatible : D.complexMap c j ≫ eA.hom = eX.hom ≫ a)
    (ha : Albanese.IsAlbaneseMap X.presentation x₀ A a) : D.IsComplexAlbanese c j := by
  have heA : IsMonHom eA.hom := inferInstance
  let : GrpObj ((Over.pullback c).obj (D.A j).X) := (D.complexAbelian c j).grp
  let : IsMonHom eA.hom := heA
  change D.complexBasePoint c j ≫ D.complexMap c j = 1 ∧ _
  constructor
  · apply (cancel_mono eA.hom).mp
    rw [Category.assoc, hcompatible, ← Category.assoc, hpoint, ha.1]
    exact (MonObj.one_comp eA.hom).symm
  · intro A' f hf
    have hf' : x₀ ≫ (eX.inv ≫ f) = 1 := by
      rw [← hpoint]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hf
    obtain ⟨φ, ⟨hφmon, hφ⟩, hφunique⟩ := ha.2 A' (eX.inv ≫ f) hf'
    let : IsMonHom φ := hφmon
    have hcomphom : IsMonHom (eA.hom ≫ φ) :=
      @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ eA.hom φ heA hφmon
    refine ⟨eA.hom ≫ φ, ⟨hcomphom, ?_⟩, ?_⟩
    · rw [← Category.assoc, hcompatible, Category.assoc, hφ]
      simp
    · intro ψ hψ
      let : IsMonHom ψ := hψ.1
      have ha' : a = eX.inv ≫ D.complexMap c j ≫ eA.hom := by
        rw [hcompatible]
        simp
      have hψ' : a ≫ (eA.inv ≫ ψ) = eX.inv ≫ f := by
        rw [ha']
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
          congrArg (fun k => eX.inv ≫ k) hψ.2
      have heq := hφunique (eA.inv ≫ ψ) ⟨inferInstance, hψ'⟩
      calc
        ψ = eA.hom ≫ (eA.inv ≫ ψ) := by simp
        _ = eA.hom ≫ φ := by rw [heq]

end

/-! The component Albanese property is invariant under actual pointed
source and group-scheme comparisons of complex fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem Components.ComponentAlbaneseData.isComplexAlbanese_of_component_iso
    {B B' : Scheme} {T : Over B} {T' : Over B'} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r) (D' : Components.ComponentAlbaneseData T' r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (c' : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B') (j : Fin r)
    (eX : D'.complexSurface c' j ≅ D.complexSurface c j)
    (eA : (D'.complexAbelian c' j).X ≅ (D.complexAbelian c j).X) [IsMonHom eA.hom]
    (hpoint : D'.complexBasePoint c' j ≫ eX.hom = D.complexBasePoint c j)
    (hcompatible : D'.complexMap c' j ≫ eA.hom = eX.hom ≫ D.complexMap c j)
    (ha : D.IsComplexAlbanese c j) : D'.IsComplexAlbanese c' j := by
  have heA : IsMonHom eA.hom := inferInstance
  have heAi : IsMonHom eA.inv := inferInstance
  let : GrpObj ((Over.pullback c').obj (D'.A j).X) := (D'.complexAbelian c' j).grp
  let : GrpObj ((Over.pullback c).obj (D.A j).X) := (D.complexAbelian c j).grp
  let : IsMonHom eA.hom := heA
  change D'.complexBasePoint c' j ≫ D'.complexMap c' j = 1 ∧ _
  constructor
  · apply (cancel_mono eA.hom).mp
    rw [Category.assoc, hcompatible, ← Category.assoc, hpoint, ha.1]
    exact (MonObj.one_comp eA.hom).symm
  · intro A f hf
    have hf' : D.complexBasePoint c j ≫ (eX.inv ≫ f) = 1 := by
      rw [← hpoint]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hf
    obtain ⟨φ, ⟨hφmon, hφ⟩, hφunique⟩ := ha.2 A (eX.inv ≫ f) hf'
    let : IsMonHom φ := hφmon
    have hmon : IsMonHom (eA.hom ≫ φ) :=
      @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ eA.hom φ heA hφmon
    refine ⟨eA.hom ≫ φ, ⟨hmon, ?_⟩, ?_⟩
    · rw [← Category.assoc, hcompatible, Category.assoc, hφ]
      simp
    · intro ψ hψ
      let : IsMonHom ψ := hψ.1
      have hm : D.complexMap c j = eX.inv ≫ D'.complexMap c' j ≫ eA.hom := by
        rw [hcompatible]
        simp
      have hψ' : D.complexMap c j ≫ (eA.inv ≫ ψ) = eX.inv ≫ f := by
        rw [hm]
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
          congrArg (fun k => eX.inv ≫ k) hψ.2
      have hback : IsMonHom (eA.inv ≫ ψ) :=
        @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ eA.inv ψ heAi hψ.1
      have heq := hφunique (eA.inv ≫ ψ) ⟨hback, hψ'⟩
      calc
        ψ = eA.hom ≫ (eA.inv ≫ ψ) := by simp
        _ = eA.hom ≫ φ := by rw [heq]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
