import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointEquivalence

/-! # Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual functor of embedded projective Hilbert families with fixed smooth relative dimension is naturally represented by the specified quasi-projective Hilbert open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_dimension
    {S T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ} (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P)
    (g : ℕ) [SmoothOfRelativeDimension g F.family.scheme.hom] (f : T ⟶ S) :
    SmoothOfRelativeDimension g (F.pullback f).family.scheme.hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
    (ClosedFamily.Transport.closedFamilyTransport_isPullback (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n) F.family.ideal)
    (inferInstance : SmoothOfRelativeDimension g F.family.scheme.hom)

def FixedDimension.Representation.fixedDimensionProjectiveHilbertFunctor (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := FixedDimension.Parameters.FixedDimensionRelativeProjectiveHilbertFamily T.unop.left n P g
  map f := TypeCat.ofHom (fun F => by
    have : SmoothOfRelativeDimension g F.val.family.scheme.hom := F.property
    exact ⟨F.val.pullback f.unop.left, F.val.pullback_dimension g f.unop.left⟩)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    exact F.val.pullback_id
  map_comp f h := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    exact (F.val.pullback_comp f.unop.left h.unop.left).symm

def FixedDimension.Representation.fixedDimensionHilbertClassifyingIso (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    yoneda.obj (FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g) ≅ FixedDimension.Representation.fixedDimensionProjectiveHilbertFunctor S n P g :=
  NatIso.ofComponents (fun T => (FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv S T.unop n P g).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    change (FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv S U.unop n P g (f.unop ≫ y)).val =
      (FixedDimension.PointEquivalence.fixedDimensionHilbertParameterPointEquiv S T.unop n P g y).val.pullback f.unop.left
    rw [← FixedDimension.PointEquivalence.fixedDimensionHilbertUniversalFamily_point, ← FixedDimension.PointEquivalence.fixedDimensionHilbertUniversalFamily_point]
    exact ((FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g).pullback_comp y.left f.unop.left).symm)

theorem FixedDimension.Representation.fixedDimensionHilbert_isRepresentable (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    (FixedDimension.Representation.fixedDimensionProjectiveHilbertFunctor S n P g).IsRepresentable :=
  Functor.IsRepresentable.mk' (FixedDimension.Representation.fixedDimensionHilbertClassifyingIso S n P g)

theorem FixedDimension.Representation.fixedDimensionHilbert_quasiProjective_representation (S : Scheme.{u}) [IsNoetherian S]
    (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (FixedDimension.Representation.fixedDimensionProjectiveHilbertFunctor S n P g ≅ yoneda.obj M) :=
  ⟨FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g, ⟨FixedDimension.Parameters.fixedDimensionHilbertParameterQuasiProjectivePresentation S n P g⟩,
    ⟨(FixedDimension.Representation.fixedDimensionHilbertClassifyingIso S n P g).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
