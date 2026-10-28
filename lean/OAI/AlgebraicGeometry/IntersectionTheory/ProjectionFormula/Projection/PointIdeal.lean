import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

/-! # Point Ideal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointIdeal

noncomputable section

section

/-! At every point the constructed projective projection acts by
contraction of the actual homogeneous prime ideal. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem constant_mem (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (c : ℂ) :
    MvPolynomial.C c ∈ x.asHomogeneousIdeal ↔ c = 0 := by
  constructor
  · intro hc
    by_contra hn
    have hu : IsUnit (MvPolynomial.C c : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) :=
      (isUnit_iff_ne_zero.mpr hn).map MvPolynomial.C
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asHomogeneousIdeal.toIdeal hc hu)
  · rintro rfl
    rw [MvPolynomial.C_0]
    exact x.asHomogeneousIdeal.toIdeal.zero_mem

theorem ideal {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    {S : Scheme} (i : S ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (hi : ∀ x, i x ∈ Projective.BasicOpen.RationalProjection.domain f)
    (hC : ∀ c : ℂ, f (MvPolynomial.C c) = MvPolynomial.C c) (x : S) :
    (Projective.ProjectionRestriction.projection f i hi x).asHomogeneousIdeal =
      (i x).asHomogeneousIdeal.comap f := by
  apply HomogeneousIdeal.ext'
  intro d p hp
  change p ∈ (Projective.ProjectionRestriction.projection f i hi x).asHomogeneousIdeal ↔
    f p ∈ (i x).asHomogeneousIdeal
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have he : MvPolynomial.C (AddMonoidAlgebra.coeff (p) (0)) = p :=
      congrArg Subtype.val ((Foundations.Scheme.ProjectiveSpace.degreeZeroConstants m).apply_symm_apply ⟨p, hp⟩)
    rw [← he, hC, constant_mem, constant_mem]
  · have he := Projective.ProjectionRestriction.preimage_basicOpen f i hi p hp hd
    have he' := (congrArg (fun U : S.Opens => x ∈ U) he).to_iff
    exact not_iff_not.mp he'

end

/-! The glued ambient rational projection contracts homogeneous
prime ideals at every point of its natural domain. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Rational

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

theorem in_domain (x : Projective.BasicOpen.RationalProjection.domain f) : (Projective.BasicOpen.RationalProjection.domain f).ι x ∈ Projective.BasicOpen.RationalProjection.domain f := x.property

theorem restriction_eq : Projective.ProjectionRestriction.projection f (Projective.BasicOpen.RationalProjection.domain f).ι (in_domain f) = Projective.BasicOpen.RationalProjection.map f := by
  have he : Projective.ProjectionRestriction.lift f (Projective.BasicOpen.RationalProjection.domain f).ι (in_domain f) = 𝟙 ((Projective.BasicOpen.RationalProjection.domain f) : Scheme) := by
    apply (cancel_mono (Projective.BasicOpen.RationalProjection.domain f).ι).mp
    rw [Projective.ProjectionRestriction.lift_fac, Category.id_comp]
  rw [Projective.ProjectionRestriction.projection, he, Category.id_comp]

theorem ideal (hC : ∀ c : ℂ, f (MvPolynomial.C c) = MvPolynomial.C c) (x : Projective.BasicOpen.RationalProjection.domain f) :
    (Projective.BasicOpen.RationalProjection.map f x).asHomogeneousIdeal = x.val.asHomogeneousIdeal.comap f := by
  have he := PointIdeal.ideal f (Projective.BasicOpen.RationalProjection.domain f).ι (in_domain f) hC x
  rw [restriction_eq] at he
  exact he

end Rational

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointIdeal
