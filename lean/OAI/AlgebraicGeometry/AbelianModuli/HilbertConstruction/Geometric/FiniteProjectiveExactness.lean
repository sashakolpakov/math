import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFieldExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulScalarExactness

/-! # Finite Projective Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiniteProjectiveExactness

noncomputable section

/-! Geometric field-valued tests detect exactness of a finite projective
complex over an affine scheme. The same test applies after an arbitrary
affine change of base, with the actual maps on global functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem affine_finiteProjectiveShortComplex_exact_of_field_points
    (S : Scheme.{u}) [IsAffine S] (C : ShortComplex (ModuleCat.{u} Γ(S, ⊤)))
    [Module.Finite Γ(S, ⊤) C.X₁] [Module.Projective Γ(S, ⊤) C.X₁]
    [Module.Finite Γ(S, ⊤) C.X₂] [Module.Projective Γ(S, ⊤) C.X₂]
    [Module.Finite Γ(S, ⊤) C.X₃] [Module.Projective Γ(S, ⊤) C.X₃]
    (h : ∀ (K : Type u) [Field K] (q : Spec (.of K) ⟶ S),
      (C.map (ModuleCat.extendScalars q.appTop.hom)).Exact) : C.Exact := by
  apply HilbertConstruction.Finite.ProjectiveFieldExactness.finiteProjectiveShortComplex_exact_of_field_tests C
  intro K _ q
  let b := Affine.QuotientCoefficientMap.affineCoordinateMap q
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have he : e.toRingHom.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective e.bijective
  have hb : ((C.map (ModuleCat.extendScalars b.appTop.hom)).map
      (ModuleCat.extendScalars e.toRingHom)).Exact :=
    (FaithfulScalarExactness.native_scalar_exact_iff_of_faithfullyFlat e.toRingHom he _).mpr (h K b)
  have hc : (C.map (ModuleCat.extendScalars (e.toRingHom.comp b.appTop.hom))).Exact :=
    (ShortComplex.exact_iff_of_iso
      (C.mapNatIso (ModuleCat.extendScalarsComp b.appTop.hom e.toRingHom))).mpr hb
  have hq : e.toRingHom.comp b.appTop.hom = q := Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap q
  rw [hq] at hc
  exact hc

theorem geometric_finiteProjectiveShortComplex_baseChange_exact
    {S Y : Scheme.{u}} [IsAffine Y] (b : Y ⟶ S)
    (C : ShortComplex (ModuleCat.{u} Γ(S, ⊤)))
    [Module.Finite Γ(S, ⊤) C.X₁] [Module.Projective Γ(S, ⊤) C.X₁]
    [Module.Finite Γ(S, ⊤) C.X₂] [Module.Projective Γ(S, ⊤) C.X₂]
    [Module.Finite Γ(S, ⊤) C.X₃] [Module.Projective Γ(S, ⊤) C.X₃]
    (h : ∀ (K : Type u) [Field K] (q : Spec (.of K) ⟶ Y),
      (C.map (ModuleCat.extendScalars (q ≫ b).appTop.hom)).Exact) :
    (letI := b.appTop.hom.toAlgebra;
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) Γ(Y, ⊤) C).Exact) := by
  let := b.appTop.hom.toAlgebra
  let B := Γ(Y, ⊤)
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) B C
  have : Module.Finite B T.X₁ := inferInstanceAs (Module.Finite B (B ⊗[Γ(S, ⊤)] C.X₁))
  have : Module.Finite B T.X₂ := inferInstanceAs (Module.Finite B (B ⊗[Γ(S, ⊤)] C.X₂))
  have : Module.Finite B T.X₃ := inferInstanceAs (Module.Finite B (B ⊗[Γ(S, ⊤)] C.X₃))
  have : Module.Projective B T.X₁ := inferInstanceAs (Module.Projective B (B ⊗[Γ(S, ⊤)] C.X₁))
  have : Module.Projective B T.X₂ := inferInstanceAs (Module.Projective B (B ⊗[Γ(S, ⊤)] C.X₂))
  have : Module.Projective B T.X₃ := inferInstanceAs (Module.Projective B (B ⊗[Γ(S, ⊤)] C.X₃))
  apply affine_finiteProjectiveShortComplex_exact_of_field_points Y T
  intro K _ q
  let := q.appTop.hom.toAlgebra
  have hc : (C.map (ModuleCat.extendScalars
      (q.appTop.hom.comp (algebraMap Γ(S, ⊤) B)))).Exact := h K q
  have hi : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex B Γ(Spec (.of K), ⊤) T).Exact :=
    (Iterated.TensorExactness.iterated_tensor_exact_iff_composite (A := B) (B := Γ(Spec (.of K), ⊤)) C).mpr hc
  exact (ShortComplex.exact_iff_of_iso
    (T.mapNatIso (Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom B Γ(Spec (.of K), ⊤) q.appTop.hom))).mp hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiniteProjectiveExactness
