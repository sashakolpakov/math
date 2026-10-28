import OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpenFiber
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteTypeCoefficientBase
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # Dedekind Geometric -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.DedekindGeometric.Construction

noncomputable section

/-! Smooth proper geometrically irreducible schemes over a number field
admit smooth proper models with geometrically irreducible fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem dedekind_good_open_has_geometric_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    [Algebra (𝓞 K) R] [Algebra.FiniteType (𝓞 K) R]
    (φ : R →ₐ[𝓞 K] K) (hφ : Function.Injective φ)
    {V M : Over (Spec (.of R))} (i : V ⟶ M) [IsOpenImmersion i.left]
    [Smooth M.hom] [IsProper M.hom] [IsIntegral M.left]
    [GeometricallyIrreducible V.hom]
    (X : Over (Spec (.of K)))
    (eM : (Over.pullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj M ≅ X) :
    ∃ N : Foundations.Constructions.CoefficientModel K X,
      Smooth N.model.hom ∧ IsProper N.model.hom ∧ GeometricallyIrreducible N.model.hom := by
  have : CompactSpace M.left := QuasiCompact.compactSpace_of_compactSpace M.hom
  have : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  obtain ⟨r, hr, hgeo⟩ := GoodOpenFiber.Construction.geometricallyIrreducible_ambient_after_shrinking R i
  let S := Localization.Away r
  have hu : IsUnit (φ r) := IsUnit.mk0 _ (by
    intro h
    exact hr (hφ (h.trans φ.map_zero.symm)))
  let ψ : S →ₐ[𝓞 K] K := IsLocalization.Away.liftAlgHom (f := φ) r hu
  let a := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let k := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let N : Over (Spec (.of S)) := (Over.pullback a).obj M
  have hka : k ≫ a = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsLocalization.Away.lift_comp r hu)
  let eN : (Over.pullback k).obj N ≅ X :=
    BaseChange.Constructions.Foundations.iteratedBaseChangeIso a k M ≪≫ Scheme.Constructions.Foundations.baseChangeCongr hka M ≪≫ eM
  have : Smooth N.hom := inferInstanceAs (Smooth (pullback.snd M.hom a))
  have : IsProper N.hom := inferInstanceAs (IsProper (pullback.snd M.hom a))
  have : GeometricallyIrreducible N.hom := hgeo
  exact FiniteTypeCoefficientBase.Construction.finiteType_geometric_model_to_coefficient_model S ψ N X eN

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.DedekindGeometric.Construction
