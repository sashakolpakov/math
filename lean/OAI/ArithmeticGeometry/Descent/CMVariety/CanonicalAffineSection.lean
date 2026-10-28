import OAI.ArithmeticGeometry.Descent.CMVariety.LocalizedFamily
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover

/-! # Canonical Affine Section -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalAffineSection.Abelian.RelativeCharts

noncomputable section

/-!
Replace an arbitrary affine open presentation by the actual section algebra
of its image. The base map and an actual algebraic section are transported
through a proved scheme isomorphism, preserving both scheme diagrams.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  {A R : Type} [CommRing A] [Algebra ℂ A] [CommRing R] [Algebra ℂ R]

theorem exists_canonical_affine_open_iso
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left] :
    ∃ (V : X.left.Opens) (hV : IsAffineOpen V),
      ∃ e : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) ≅ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A,
        e.hom ≫ i = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV := by
  let : IsAffine (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let V := i.left.opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange i.left
  let j := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  have hrange : Set.range j.left = Set.range i.left := hV.range_fromSpec
  let e := IsOpenImmersion.isoOfRangeEq j.left i.left hrange
  have he : e.hom ≫ i.left = j.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hw : e.hom ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).hom =
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)).hom := by
    rw [← i.w, ← Category.assoc, he]
    exact j.w
  refine ⟨V, hV, Over.isoMk e hw, ?_⟩
  apply Over.OverMorphism.ext
  exact he

/-- The actual section and projection give a retraction on the canonical
affine section algebra. No choice of analytic coordinates is involved. -/
theorem exists_canonical_affine_section_diagram
    (p : X ⟶ S) (sectionMap : S ⟶ X) (hsection : sectionMap ≫ p = 𝟙 S)
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (f : R →ₐ[ℂ] A) (σ : A →ₐ[ℂ] R)
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A f ≫ b)
    (hσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A R σ ≫ i = b ≫ sectionMap) :
    ∃ (V : X.left.Opens) (hV : IsAffineOpen V)
      (a : Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)),
      letI := a
      ∃ ht : IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V),
      letI := ht
      ∃ σ' : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V →ₐ[ℂ] R,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV ≫ p =
          AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
            (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)) ≫ b ∧
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) R σ' ≫
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV = b ≫ sectionMap ∧
        σ'.comp (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)) = AlgHom.id ℂ R := by
  obtain ⟨V, hV, e, he⟩ := exists_canonical_affine_open_iso i
  let C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let j := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  change e.hom ≫ i = j at he
  let f' : R →ₐ[ℂ] C := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R C).symm
    (e.hom ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A f)
  let σ' : C →ₐ[ℂ] R := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C R).symm
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A R σ ≫ e.inv)
  have hf' : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R C f' =
      e.hom ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A f := Equiv.apply_symm_apply _ _
  have hσ' : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C R σ' =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A R σ ≫ e.inv := Equiv.apply_symm_apply _ _
  let a : Algebra R C := f'.toRingHom.toAlgebra
  let : Algebra R C := a
  have ht : IsScalarTower ℂ R C :=
    IsScalarTower.of_algebraMap_eq (fun c => (f'.commutes c).symm)
  let : IsScalarTower ℂ R C := ht
  have hbase : IsScalarTower.toAlgHom ℂ R C = f' := by ext r; rfl
  have hj : j ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R C f' ≫ b := by
    rw [← he, Category.assoc, hi, hf', Category.assoc]
  have hs : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C R σ' ≫ j = b ≫ sectionMap := by
    rw [hσ', ← he]
    simpa only [Category.assoc, e.inv_hom_id_assoc] using hσ
  have hret : σ'.comp f' = AlgHom.id ℂ R := by
    apply (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R R).injective
    have hid : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R R (AlgHom.id ℂ R) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      change Spec.map (𝟙 (CommRingCat.of R)) = 𝟙 _
      simp
    rw [← LocalizedFamily.Abelian.RelativeCharts.affineSpec_comp, hid]
    apply Over.OverMorphism.ext
    apply (cancel_mono b.left).mp
    have h : (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C R σ' ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R C f') ≫ b = b := by
      rw [Category.assoc, ← hj, ← Category.assoc, hs, Category.assoc, hsection, Category.comp_id]
    exact congrArg Over.Hom.left h
  refine ⟨V, hV, a, ht, σ', ?_⟩
  change (j ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R C (IsScalarTower.toAlgHom ℂ R C) ≫ b) ∧
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C R σ' ≫ j = b ≫ sectionMap) ∧
    σ'.comp (IsScalarTower.toAlgHom ℂ R C) = AlgHom.id ℂ R
  rw [hbase]
  exact ⟨hj, hs, hret⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalAffineSection.Abelian.RelativeCharts
