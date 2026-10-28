import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.CoordinateAlgebra
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousFormJets

/-! # Point Jets -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets

noncomputable section

section

/-! At every point of a closed projective subscheme, homogeneous
linear forms surject onto the value and tangent data of the actual stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra

variable {X : Scheme} (n : ℕ) (i : Fin (n + 1)) (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)

def coordinateGerm (x : X) (hx : j x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    letI := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x
    Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i →ₐ[ℂ] X.presheaf.stalk x := by
  let U := j ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) U
  let := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x
  exact (Stalk.ScalarMaps.germ (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) U x hx).comp
    (CoordinateAlgebra.quotientMap n i j)

def map (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) = 𝟙 _)
    (hx : j (p (IsLocalRing.closedPoint ℂ)) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    letI := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (p (IsLocalRing.closedPoint ℂ))
    Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] ℂ ×
      (AugmentedCotangent.ideal (Stalk.PointAlgebra.evaluation (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) p hp)).Cotangent := by
  let := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) (p (IsLocalRing.closedPoint ℂ))
  exact HomogeneousFormJets.map n i (coordinateGerm n i j _ hx)
    (Stalk.PointAlgebra.evaluation (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) p hp)

theorem surjective [IsClosedImmersion j]
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) = 𝟙 _)
    (hx : j (p (IsLocalRing.closedPoint ℂ)) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    Function.Surjective (map n i j p hp hx) := by
  let x := p (IsLocalRing.closedPoint ℂ)
  let U := j ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  let hU : IsAffineOpen U := (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i).preimage j
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) U
  let := Stalk.PointAlgebra.scalarAlgebra (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  let : IsScalarTower ℂ Γ(X, U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((Stalk.ScalarMaps.germ (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) U x hx).commutes c).symm
  let M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization M (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
  exact HomogeneousFormJets.surjective_of_localization n i
    (Stalk.PointAlgebra.evaluation (j ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) p hp) M
    (CoordinateAlgebra.quotientMap n i j)
    (CoordinateAlgebra.quotientMap_surjective n i j)

end

/-! Ratios of linear forms as elements of the actual projective stalk,
with the cancellation identities needed for projection coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace StalkFractions

variable (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n)

def fraction (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ x.asHomogeneousIdeal) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.stalk x :=
  (Proj.stalkIso' (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) x).symm
    (HomogeneousLocalization.mk ⟨1, a, s, hs⟩)

theorem germ (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ x.asHomogeneousIdeal) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.germ (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val) x hs
      (Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val
        (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.property 1 a.val a.property)) = fraction n x a s hs := by
  apply (Proj.stalkIso' (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) x).injective
  rw [fraction, RingEquiv.apply_symm_apply]
  refine (Proj.stalkIso'_germ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val) x hs
    (Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.val
      (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.property 1 a.val a.property))).trans ?_
  change HomogeneousLocalization.mapId (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Submonoid.powers_le.mpr hs)
    (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) s.property 1 a.val a.property) = _
  simp only [Away.mk, mapId, HomogeneousLocalization.map_mk, pow_one]
  rfl

theorem self (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hs : s.val ∉ x.asHomogeneousIdeal) :
    fraction n x s s hs = 1 := by
  apply (Proj.stalkIso' (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) x).injective
  rw [fraction, RingEquiv.apply_symm_apply, map_one]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨s.val, hs⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

theorem mul (a s t : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hs : s.val ∉ x.asHomogeneousIdeal) (ht : t.val ∉ x.asHomogeneousIdeal) :
    fraction n x a s hs * fraction n x s t ht = fraction n x a t ht := by
  apply (Proj.stalkIso' (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) x).injective
  simp only [map_mul, fraction, RingEquiv.apply_symm_apply]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
  ring

theorem isUnit (a s : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (ha : a.val ∉ x.asHomogeneousIdeal) (hs : s.val ∉ x.asHomogeneousIdeal) :
    IsUnit (fraction n x a s hs) := by
  apply IsUnit.of_mul_eq_one (fraction n x s a ha)
  rw [mul, self]

end StalkFractions

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.PointJets
