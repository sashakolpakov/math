import OAI.ArithmeticGeometry.Descent.CMVariety.CanonicalAffineSection

/-! # Affine Family Neighborhood -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AffineFamilyNeighborhood.Abelian.RelativeCharts

noncomputable section

/-!
Construct an actual affine total-space neighborhood over a chosen affine
base open. The relative algebra structure and its commuting scheme diagram
come from the universal property of the open immersion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {R : Type} [CommRing R] [Algebra ℂ R]

theorem exists_affine_diagram_over_open
    (p : X ⟶ S) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (ht : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p t ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b)) :
    ∃ (A : CommAlgCat ℂ) (a : Algebra R A),
      letI := a
      ∃ tower : IsScalarTower ℂ R A,
      letI := tower
      ∃ i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X,
        IsOpenImmersion i.left ∧
        i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b ∧
        t ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) := by
  let W := p.left ⁻¹ᵁ b.left.opensRange
  have htW : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying t ∈ W := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion] at ht
    exact ht
  obtain ⟨V, hV, htV, hVW⟩ := exists_isAffineOpen_mem_and_subset htW
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV
  have hrange : Set.range (i.left ≫ p.left) ⊆ Set.range b.left := by
    rintro z ⟨w, rfl⟩
    have hw : i.left w ∈ V := by
      change i.left w ∈ (V : Set X.left)
      rw [← hV.range_fromSpec]
      exact ⟨w, rfl⟩
    exact hVW hw
  let l := IsOpenImmersion.lift b.left (i.left ≫ p.left) hrange
  have hl : l ≫ b.left = i.left ≫ p.left := IsOpenImmersion.lift_fac _ _ _
  have hlover : l ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).hom = (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).hom := by
    rw [← b.w, ← Category.assoc, hl, Category.assoc, p.w]
    exact i.w
  let f := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A).symm (Over.homMk l hlover)
  have hf : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A f = Over.homMk l hlover := Equiv.apply_symm_apply _ _
  let a : Algebra R A := f.toRingHom.toAlgebra
  let : Algebra R A := a
  have tower : IsScalarTower ℂ R A :=
    IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  let : IsScalarTower ℂ R A := tower
  have hbase : IsScalarTower.toAlgHom ℂ R A = f := by ext r; rfl
  refine ⟨A, a, tower, i, inferInstance, ?_, ?_⟩
  · rw [hbase, hf]
    apply Over.OverMorphism.ext
    exact hl.symm
  · change t ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV)
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    exact htV

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AffineFamilyNeighborhood.Abelian.RelativeCharts
