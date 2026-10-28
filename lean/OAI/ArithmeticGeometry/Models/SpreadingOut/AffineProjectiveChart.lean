import OAI.ArithmeticGeometry.Models.SpreadingOut.ProjectiveEmbedding
import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenOver

/-! # Affine Projective Chart -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AffineProjectiveChart.Construction

noncomputable section

/-! Any affine finite-type scheme embeds as a closed subscheme of an open
chart in the generic fiber of an integral projective-space model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affine_has_closed_generic_projective_chart
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : Over (Spec (.of K))) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ (n : ℕ)
      (V : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (ProjectiveEmbedding.Construction.projectiveModel R n)).left.Opens)
      (e : X ⟶ OpenOver.Construction.overOpen
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
          (ProjectiveEmbedding.Construction.projectiveModel R n)) V),
      IsClosedImmersion e.left := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra K A := φ.hom.toAlgebra
  have hφFT : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Algebra.FiniteType K A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hφFT
  let eX : X ≅ Affine.Construction.affineOver K A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  obtain ⟨n, i, hi⟩ := ProjectiveEmbedding.Construction.affine_finiteType_has_projective_chart_embedding K A
  have := hi
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let P := (Over.pullback g).obj (ProjectiveEmbedding.Construction.projectiveModel R n)
  let j := ProjectiveEmbedding.Construction.projectiveGenericChartHom R K n 0
  have : IsOpenImmersion j.left := ProjectiveEmbedding.Construction.projectiveGenericChartHom_openImmersion R K n 0
  let V := j.left.opensRange
  let v : Spec (.of (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := K) n 0)) ≅
      V.toScheme :=
    IsOpenImmersion.isoOfRangeEq j.left V.ι (by rw [Scheme.Opens.range_ι]; rfl)
  have hv : v.hom ≫ V.ι = j.left :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let eV : Affine.Construction.affineOver K (Projective.Construction.ProjectiveConstruction.projectiveChartPolynomial (K := K) n 0) ≅
      OpenOver.Construction.overOpen P V := Over.isoMk v (by
    change v.hom ≫ (V.ι ≫ P.hom) = _
    rw [← Category.assoc, hv]
    exact j.w)
  have : IsIso eX.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eX.hom))
  have : IsIso eV.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eV.hom))
  refine ⟨n, V, eX.hom ≫ i ≫ eV.hom, ?_⟩
  change IsClosedImmersion (eX.hom.left ≫ i.left ≫ eV.hom.left)
  infer_instance

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AffineProjectiveChart.Construction
