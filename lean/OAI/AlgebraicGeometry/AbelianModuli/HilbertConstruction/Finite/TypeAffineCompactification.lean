import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CompactificationPresentation

/-! # Type Affine Compactification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeAffineCompactification.AffineCompactification

noncomputable section

/-! Finite generation suffices for affine projective compactification over an arbitrary ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A σ : Type u} [CommRing R] [CommRing A] [Algebra R A]

def allRelationsPresentation (G : Algebra.Generators R A σ) :
    Algebra.Presentation R A σ G.ker where
  __ := G
  relation := Subtype.val
  span_range_relation_eq_ker := by
    rw [Subtype.range_coe_subtype]
    exact Ideal.span_eq G.ker

def ofFiniteTypeAlgebra (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    Affine.Compactification.AffineCompactification.Data (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let s : Finset A := (Algebra.FiniteType.out (R := R) (A := A)).choose
  have hs : Algebra.adjoin R (s : Set A) = ⊤ :=
    (Algebra.FiniteType.out (R := R) (A := A)).choose_spec
  exact Affine.Compactification.AffineCompactification.ofPresentation (allRelationsPresentation (Algebra.Generators.ofSet hs))

def ofAffineFiniteType {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : Affine.Compactification.AffineCompactification.Data f := by
  let : Algebra R Γ(X, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap f).toAlgebra
  have hf : f.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have hc : (Coefficient.ModulePresheaf.schemeCoefficientMap f).FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv f.appTop).mpr hf
  have : Algebra.FiniteType R Γ(X, ⊤) := hc
  let D := ofFiniteTypeAlgebra (R := R) Γ(X, ⊤)
  refine ⟨D.coordinates, D.finiteCoordinates, D.scheme, D.base, D.proper,
    X.isoSpec.hom ≫ D.chart, inferInstance, ?_,
    D.embedding, D.closedImmersion, D.embedding_base⟩
  rw [Category.assoc, D.chart_base]
  exact Affine.Compactification.AffineCompactification.coefficient_factor f

def affineFiniteTypeQuasiProjectiveOverRing {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk f) :=
  (ofAffineFiniteType f).quasiProjectivePresentation

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeAffineCompactification.AffineCompactification
