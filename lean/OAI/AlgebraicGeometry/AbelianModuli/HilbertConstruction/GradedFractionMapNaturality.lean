import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCoordinateEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMaps

/-! # Graded Fraction Map Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedFractionMapNaturality

noncomputable section

/-! The actual homogeneous-fraction morphisms commute with a graded
map after transforming coordinate values. This includes linear coordinate
changes and supplies their local comparison with section-defined maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}
variable (g : Projective.ProjectivePresentations.coordinateGrading R n →+*ᵍ Projective.ProjectivePresentations.coordinateGrading R n)
variable (hg : ∀ r : R, g (MvPolynomial.C r) = MvPolynomial.C r)
variable (c : R →+* B) (v : Fin (n + 1) → B)

include hg in
theorem homogeneousFractionEvaluation_gradedMap (f : Projective.ProjectivePresentations.coordinateRing R n) (d : ℕ)
    (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d)
    (hf : IsUnit (MvPolynomial.eval₂Hom c (GradedCoordinateEvaluation.gradedCoordinateValues g c v) f))
    (hgF : IsUnit (MvPolynomial.eval₂Hom c v (g f))) :
    (Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hgF).comp (HomogeneousLocalization.Away.map g f) =
      Homogeneous.Fractions.homogeneousFractionEvaluation c (GradedCoordinateEvaluation.gradedCoordinateValues g c v) f hf := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hf
  have hga : MvPolynomial.eval₂Hom c v (g f) * a = 1 :=
    (congrArg (fun x => x * a) (GradedCoordinateEvaluation.gradedCoordinateEvaluation_apply g hg c v f)).trans ha
  apply RingHom.ext
  intro z
  obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (Projective.ProjectivePresentations.coordinateGrading R n) hfd z
  change Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hgF
    (HomogeneousLocalization.Away.map g f (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R n) hfd k p hp)) = _
  rw [HomogeneousLocalization.Away.map_mk]
  exact (Homogeneous.Fractions.homogeneousFractionEvaluation_mk c v (g f) hgF d (g.map_mem hfd) k (g p) (g.map_mem hp) a hga).trans
    ((congrArg (fun q => q * a ^ k) (GradedCoordinateEvaluation.gradedCoordinateEvaluation_apply g hg c v p)).trans
      (Homogeneous.Fractions.homogeneousFractionEvaluation_mk c (GradedCoordinateEvaluation.gradedCoordinateValues g c v) f hf d hfd k p hp a ha).symm)

variable {T : Scheme.{u}}

include hg in
theorem projectiveFractionMap_gradedMap
    (hi : HomogeneousIdeal.irrelevant (Projective.ProjectivePresentations.coordinateGrading R n) ≤
      (HomogeneousIdeal.irrelevant (Projective.ProjectivePresentations.coordinateGrading R n)).map g)
    (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤)) (f : Projective.ProjectivePresentations.coordinateRing R n) (d : ℕ)
    (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d) (hd : 0 < d)
    (hf : IsUnit (MvPolynomial.eval₂Hom c (GradedCoordinateEvaluation.gradedCoordinateValues g c v) f))
    (hgF : IsUnit (MvPolynomial.eval₂Hom c v (g f))) :
    Chart.OverlapMaps.projectiveFractionMap c v (g f) hgF d (g.map_mem hfd) hd ≫ Proj.map g hi =
      Chart.OverlapMaps.projectiveFractionMap c (GradedCoordinateEvaluation.gradedCoordinateValues g c v) f hf d hfd hd := by
  have he := homogeneousFractionEvaluation_gradedMap g hg c v f d hfd hf hgF
  change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hgF)) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (g f) (g.map_mem hfd) hd) ≫ Proj.map g hi = _
  rw [Category.assoc, Category.assoc, Proj.awayι_comp_map g hi hd f hfd, ← Spec.map_comp_assoc]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hgF).comp (HomogeneousLocalization.Away.map g f))) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd = _
  rw [he]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedFractionMapNaturality
