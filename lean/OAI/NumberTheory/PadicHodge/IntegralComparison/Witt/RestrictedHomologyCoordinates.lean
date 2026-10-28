import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

/-! # Restricted Homology Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RestrictedHomologyCoordinates

noncomputable section

/-! Scalar restriction and the original Witt coefficient coordinates
carry homology maps to their actual additive maps. -/
open _root_.CategoryTheory _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
  (S : Type u) [CommRing S] [Algebra (WittVector p k) S]

abbrev restriction := ModuleCat.restrictScalars (algebraMap (WittVector p k) S)
abbrev mapped (K : CochainComplex (ModuleCat.{u} S) ℕ) :=
  ((restriction p k S).mapHomologicalComplex (.up ℕ)).obj K

def coordinate (K : CochainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :=
  (CoefficientCoordinates.addEquiv p k ((mapped p k S K).homology q)).toAddMonoidHom.comp
    (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (restriction p k S) K q).toLinearEquiv.toAddEquiv.symm.toAddMonoidHom

variable {K L : CochainComplex (ModuleCat.{u} S) ℕ} (a : K ⟶ L) (q : ℕ)

theorem inverse_natural (x : K.homology q) :
    (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (restriction p k S) L q).inv (homologyMap a q x) =
      homologyMap (((restriction p k S).mapHomologicalComplex (.up ℕ)).map a) q
        ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (restriction p k S) K q).inv x) :=
  ConcreteCategory.congr_hom
    (ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor (ModuleCat.{u} S) (.up ℕ) q).map a) (restriction p k S)) x

theorem naturality (x : K.homology q) :
    coordinate p k S L q (homologyMap a q x) =
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (homologyMap (((restriction p k S).mapHomologicalComplex (.up ℕ)).map a) q)
        (coordinate p k S K q x) := by
  change CoefficientCoordinates.addEquiv p k _
      ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (restriction p k S) L q).inv (homologyMap a q x)) =
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map _
      (CoefficientCoordinates.addEquiv p k _
        ((AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso (restriction p k S) K q).inv x))
  rw [CoefficientCoordinates.map_apply, inverse_natural]

variable {T : ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
  (c : (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).obj
    ((mapped p k S L).homology q) ⟶ T)
  (d : (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).obj
    ((mapped p k S K).homology q) ⟶ T)

include c d in
theorem comparison
    (h : (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (((restriction p k S).mapHomologicalComplex (.up ℕ)).map a) q) ≫ c = d)
    (x : K.homology q) :
    c (coordinate p k S L q (homologyMap a q x)) = d (coordinate p k S K q x) := by
  rw [naturality]
  exact ConcreteCategory.congr_hom h (coordinate p k S K q x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RestrictedHomologyCoordinates
