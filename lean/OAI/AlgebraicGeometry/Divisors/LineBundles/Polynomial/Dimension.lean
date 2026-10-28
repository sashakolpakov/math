import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual polynomial charts raise the support transcendence dimension by one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

theorem polynomial_trdeg_toNat (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    (Algebra.trdeg k (Polynomial R)).toNat = (Algebra.trdeg k R).toNat + 1 := by
  have ht := trdeg_add_eq k R (A := Polynomial R)
  have hfin : Algebra.trdeg k R < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  rw [Polynomial.trdeg_of_isDomain] at ht
  rw [← ht, Cardinal.toNat_add hfin (by simp)]
  simp

/-- An actual polynomial chart determines the global dimension increase. -/
theorem polynomial_dimension_of_chart (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R]
    {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (a : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion a]
    (b : Spec (CommRingCat.of (Polynomial R)) ⟶ B) [IsOpenImmersion b]
    (g : B ⟶ A)
    (h : b ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) ≫ a)
    (f : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (g ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let α : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (a ≫ f)
  let : Algebra k R := α.hom.toAlgebra
  have hα : Spec.map α = a ≫ f := Spec.map_preimage _
  have hfα : LocallyOfFiniteType (Spec.map α) :=
    (congrArg (fun q => LocallyOfFiniteType q) hα).mpr inferInstance
  have : Algebra.FiniteType k R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfα
  let c : CommRingCat.of R ⟶ CommRingCat.of (Polynomial R) :=
    CommRingCat.ofHom (algebraMap R (Polynomial R))
  have hαc : α ≫ c = CommRingCat.ofHom (algebraMap k (Polynomial R)) := rfl
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) =
      Spec.map c ≫ (a ≫ f) :=
    (congrArg Spec.map hαc.symm).trans
      ((Spec.map_comp α c).trans (congrArg (fun q => Spec.map c ≫ q) hα))
  have hb : b ≫ (g ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ f) h).trans ((Category.assoc _ _ _).trans hspec.symm))
  have haDim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = (Algebra.trdeg k R).toNat :=
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion a f).symm.trans
      ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hα.symm).trans
        (Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k R))
  exact (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion b (g ≫ f)).symm.trans
    ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hb).trans
    ((Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k (Polynomial R)).trans
    ((polynomial_trdeg_toNat k R).trans (congrArg (fun n => n + 1) haDim.symm))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension.BundleCycles
