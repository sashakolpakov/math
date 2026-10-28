import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.TestFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ParameterIsoFactorization

/-! # Spectrum Test Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumTestFactorization

noncomputable section

/-! Testing factorizations on spectra of rings suffices to test them
on every affine scheme, including its actual structure map to the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {M Z : Over S}

theorem affine_lifts_of_spectrum_tests (F : Subfunctor (yoneda.obj M)) (j : Z ⟶ M)
    (hspec : ∀ (A : Type u) [CommRing A] (a : Spec (CommRingCat.of A) ⟶ S)
      (x : Over.mk a ⟶ M), x ∈ F.obj (.op (Over.mk a)) ↔ ∃ y : Over.mk a ⟶ Z, y ≫ j = x)
    (T : Over S) [IsAffine T.left] (x : T ⟶ M) :
    x ∈ F.obj (.op T) ↔ ∃ y : T ⟶ Z, y ≫ j = x := by
  let e₀ := T.left.isoSpec
  let V : Over S := Over.mk (e₀.inv ≫ T.hom)
  let e : T ≅ V := Over.isoMk e₀ (Iso.hom_inv_id_assoc e₀ T.hom)
  have h := hspec Γ(T.left, ⊤) (e₀.inv ≫ T.hom) (e.inv ≫ x)
  exact (ParameterIsoFactorization.subfunctor_mem_comp_iso_iff F e.symm x).symm.trans
    (h.trans (ParameterIsoFactorization.exists_lift_comp_iso_iff e.symm j x))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumTestFactorization
