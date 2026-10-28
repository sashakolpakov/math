import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GlobalScalarEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothDiagonalCoordinates
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Etale Affine Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleAffineNeighborhood.Constructions

noncomputable section

/-! Every point of a smooth integral affine complex scheme has an
actual affine open neighborhood with etale polynomial coordinates on
its genuine global-section algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GlobalScalarEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_etale_affine_neighborhood (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [IsIntegral X.left] [Smooth X.hom] (x : X.left) :
    ∃ Y : Over Foundations.Scheme.ProjectiveSpace.complexBase, ∃ hY : IsAffine Y.left, letI := hY
      ∃ j : Y ⟶ X, IsOpenImmersion j.left ∧ IsIntegral Y.left ∧ Smooth Y.hom ∧
        (∃ y : Y.left, j.left y = x) ∧
        ∃ n : ℕ, ∃ a : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y.left, ⊤), letI := a
          IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y.left, ⊤) ∧
            Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) Γ(Y.left, ⊤) := by
  let R := Γ(X.left, ⊤)
  let q : PrimeSpectrum R := X.left.isoSpec.hom x
  obtain ⟨f, hf, n, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := ℂ) (p := q.asIdeal)
  have hf0 : f ≠ 0 := by
    intro h
    apply hf
    rw [h]
    exact q.asIdeal.zero_mem
  let S := Localization.Away f
  let := a
  let := ht
  let := he
  let : IsDomain S := Localization.Away.isDomain hf0
  let Y := Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S
  let hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of S)))
  let : IsIntegral Y.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of S)))
  let g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⟶ Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R :=
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R S (IsScalarTower.toAlgHom ℂ R S)
  let j : Y ⟶ X := g ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv
  have hg : IsOpenImmersion g.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    exact IsOpenImmersion.of_isLocalization f
  let : IsOpenImmersion j.left := by
    change IsOpenImmersion (g.left ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv.left)
    infer_instance
  have hsmooth : Smooth Y.hom := by
    rw [← j.w]
    infer_instance
  have hq : q ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    change q ∈ Set.range (PrimeSpectrum.comap (algebraMap R S))
    rw [PrimeSpectrum.localization_away_comap_range S f]
    exact hf
  obtain ⟨y, hy⟩ := hq
  have hjy : j.left y = x := by
    change X.left.isoSpec.inv ((Spec.map (CommRingCat.ofHom (algebraMap R S))) y) = x
    rw [hy]
    exact congrArg (fun f : X.left ⟶ X.left => f x) X.left.isoSpec.hom_inv_id
  obtain ⟨ac, htc, hec⟩ := Affine.GlobalScalarEquiv.Constructions.exists_global_etale_coordinates S n
  exact ⟨Y, hY, j, inferInstance, inferInstance, hsmooth, ⟨y, hjy⟩, n, ac, htc, hec⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleAffineNeighborhood.Constructions
