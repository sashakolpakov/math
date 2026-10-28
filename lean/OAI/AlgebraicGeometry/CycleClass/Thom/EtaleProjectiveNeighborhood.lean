import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleAffineNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateDimension

/-! # Etale Projective Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood.Constructions

noncomputable section

/-! Actual affine etale neighborhoods of arbitrary scheme points in a
smooth projective variety, with the coordinate count fixed by its dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleAffineNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateDimension.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_etale_projective_neighborhood (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : V.carrier) :
    ∃ Y : Over Foundations.Scheme.ProjectiveSpace.complexBase, ∃ hY : IsAffine Y.left, letI := hY
      ∃ j : Y ⟶ V.toOver, IsOpenImmersion j.left ∧ IsIntegral Y.left ∧ Smooth Y.hom ∧
        (∃ y : Y.left, j.left y = x) ∧
        ∃ a : Algebra (MvPolynomial (Fin V.complexDimension) ℂ) Γ(Y.left, ⊤), letI := a
          IsScalarTower ℂ (MvPolynomial (Fin V.complexDimension) ℂ) Γ(Y.left, ⊤) ∧
            Algebra.IsStandardEtale (MvPolynomial (Fin V.complexDimension) ℂ) Γ(Y.left, ⊤) := by
  obtain ⟨i, xi, hxi⟩ := V.carrier.affineCover.exists_eq x
  let : Nonempty (V.carrier.affineCover.X i) := ⟨xi⟩
  let : IsIntegral (V.carrier.affineCover.X i) :=
    isIntegral_of_isOpenImmersion (V.carrier.affineCover.f i)
  let X := Over.mk (V.carrier.affineCover.f i ≫ V.structureMap)
  let : IsAffine X.left := Scheme.isAffine_affineCover V.carrier i
  let : IsIntegral X.left := inferInstanceAs (IsIntegral (V.carrier.affineCover.X i))
  let : Smooth X.hom := inferInstanceAs (Smooth (V.carrier.affineCover.f i ≫ V.structureMap))
  let jX : X ⟶ V.toOver := Over.homMk (V.carrier.affineCover.f i)
  obtain ⟨Y, hY, j, hj, hI, hS, ⟨y, hy⟩, n, a, ht, he⟩ :=
    EtaleAffineNeighborhood.Constructions.exists_etale_affine_neighborhood X xi
  let := hY
  let := hj
  let := hI
  let := hS
  let := a
  let := ht
  let := he
  let k : Y ⟶ V.toOver := j ≫ jX
  let : IsOpenImmersion k.left := by
    change IsOpenImmersion (j.left ≫ V.carrier.affineCover.f i)
    infer_instance
  have hn := EtaleCoordinateDimension.Constructions.open_coordinate_dimension V Y k n
  have hk : k.left y = x := by
    change V.carrier.affineCover.f i (j.left y) = x
    rw [hy]
    exact hxi
  refine ⟨Y, hY, k, inferInstance, hI, hS, ⟨y, hk⟩, ?_⟩
  rw [← hn]
  exact ⟨a, ht, he⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleProjectiveNeighborhood.Constructions
