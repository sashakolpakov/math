import OAI.AlgebraicGeometry.ComplexPoints.AffineClosed
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Scheme Closed -/

namespace OAI.AlgebraicGeometry.ComplexPoints.SchemeClosed.ClosednessConstruction

/-! Closedness: algebraic closedness detection on arbitrary finite-type complex schemes. -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Closedness detection transported through the canonical affine presentation. -/
theorem affineScheme_locallyClosed_isClosed_of_analytic
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (S : Set X.left) (hS : IsLocallyClosed S)
    (hA : IsClosed (Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S)) : IsClosed S := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  have hclosed : IsClosed (X.left.isoSpec.inv ⁻¹' S) := by
    apply AffineClosed.ClosednessConstruction.affine_locallyClosed_isClosed_of_analytic _
      (hS.preimage X.left.isoSpec.inv.continuous)
    have h := hA.preimage (Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X).symm.continuous
    convert h using 1
    ext x
    change X.left.isoSpec.inv (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x) ∈ S ↔
      Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ Γ(X.left, ⊤)) (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv x) ∈ S
    rw [Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap]
    rfl
  have himage := X.left.isoSpec.inv.isClosedMap _ hclosed
  rwa [Set.image_preimage_eq _ X.left.isoSpec.inv.surjective] at himage

/-- For a locally closed subset of a complex scheme locally of finite type,
closedness of its ordinary complex points implies Zariski closedness. -/
theorem scheme_locallyClosed_isClosed_of_analytic
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    (S : Set X.left) (hS : IsLocallyClosed S)
    (hA : IsClosed (Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S)) : IsClosed S := by
  have hlocal (i : X.left.affineCover.I₀) :
      IsClosed (X.left.affineCover.f i ⁻¹' S) := by
    let V := Analytic.SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X X.left.affineCover i
    let j : V ⟶ X := Analytic.SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion X X.left.affineCover i
    let : IsAffine V.left := inferInstanceAs (IsAffine (X.left.affineCover.X i))
    let : LocallyOfFiniteType V.hom :=
      inferInstanceAs (LocallyOfFiniteType (X.left.affineCover.f i ≫ X.hom))
    apply affineScheme_locallyClosed_isClosed_of_analytic V _
      (hS.preimage (X.left.affineCover.f i).continuous)
    have h := hA.preimage (Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map j)
    convert h using 1
    ext p
    exact Iff.rfl
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨i, y, rfl⟩ := X.left.affineCover.exists_eq x
  have hopen := (X.left.affineCover.f i).isOpenMap _ (hlocal i).isOpen_compl
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨y, hx, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact hz

/-- An immersion with analytically closed image is an algebraic closed immersion. -/
theorem immersion_isClosedImmersion_of_analytic_image
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsImmersion i.left]
    (hi : IsClosed (Set.range (Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i))) : IsClosedImmersion i.left := by
  apply IsClosedImmersion.of_isPreimmersion
  apply scheme_locallyClosed_isClosed_of_analytic Y _ i.left.isLocallyClosed_range
  rwa [← Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion i]

end OAI.AlgebraicGeometry.ComplexPoints.SchemeClosed.ClosednessConstruction
