import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Refinement

noncomputable section

/-!
# ChernClass: refinement of rational Cech total complexes

Every map here restricts actual sections along inclusions of open intersections.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {T I J : Type} [TopologicalSpace T]
variable (U : I → Opens T) (V : J → Opens T) (r : J → I) (hr : ∀ j, V j ≤ U (r j))

/-- Refinement commutes with morphisms of the coefficient presheaves. -/
theorem cechCoefficientMap_refinement
    {F G : (Opens T)ᵒᵖ ⥤ ModuleCat ℚ} (α : F ⟶ G)
    (n : ℕ) (c : Rational.Cech.RationalCech.CechCochain F U n) :
    Rational.Cech.RationalCech.cechCoefficientMap V α n (Rational.Cech.RationalCech.cechRefinementMap F U V r hr n c) =
      Rational.Cech.RationalCech.cechRefinementMap G U V r hr n (Rational.Cech.RationalCech.cechCoefficientMap U α n c) := by
  funext a
  exact congrArg (fun f => f.hom (c (r ∘ a)))
    (α.naturality (homOfLE (Rational.Cech.RationalCech.cechIntersection_refinement_le U V r hr a)).op)

variable (K : CochainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat ℚ) ℕ)

/-- Restriction of coefficient complexes on every intersection. -/
def cechColumnRefinement (p : ℕ) : (Rational.Cech.RationalCech.cechDoubleComplex U K).X p ⟶
    (Rational.Cech.RationalCech.cechDoubleComplex V K).X p :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom (Rational.Cech.RationalCech.cechRefinementMap (K.X q) U V r hr p))
    (fun q => by
      rw [Rational.Cech.RationalCech.cechDoubleComplex_X_d, Rational.Cech.RationalCech.cechDoubleComplex_X_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact cechCoefficientMap_refinement U V r hr (K.d q (q + 1)) p c)

/-- Restriction gives a morphism of the actual double complexes. -/
def cechDoubleComplexRefinement : Rational.Cech.RationalCech.cechDoubleComplex U K ⟶ Rational.Cech.RationalCech.cechDoubleComplex V K :=
  CochainComplex.ofHom (cechColumnRefinement U V r hr K)
    (fun p => by
      apply HomologicalComplex.Hom.ext
      funext q
      change (cechColumnRefinement U V r hr K p).f q ≫
          ((Rational.Cech.RationalCech.cechDoubleComplex V K).d p (p + 1)).f q =
        ((Rational.Cech.RationalCech.cechDoubleComplex U K).d p (p + 1)).f q ≫
          (cechColumnRefinement U V r hr K (p + 1)).f q
      rw [Rational.Cech.RationalCech.cechDoubleComplex_d_f, Rational.Cech.RationalCech.cechDoubleComplex_d_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (Rational.Cech.RationalCech.cechRefinementMap_delta (K.X q) U V r hr p c).symm)

/-- The signed total-complex refinement is induced by actual restriction. -/
def cechTotalRefinement : Rational.Cech.RationalCech.cechTotalComplex U K ⟶ Rational.Cech.RationalCech.cechTotalComplex V K :=
  HomologicalComplex₂.total.map (cechDoubleComplexRefinement U V r hr K) (ComplexShape.up ℕ)

/-- The total refinement restricts each genuine section summand. -/
theorem cechTotalInclusion_refinement (p q n : ℕ) (h : p + q = n) :
    Rational.Cech.RationalCech.cechTotalInclusion U K p q n h ≫ (cechTotalRefinement U V r hr K).f n =
      ModuleCat.ofHom (Rational.Cech.RationalCech.cechRefinementMap (K.X q) U V r hr p) ≫
        Rational.Cech.RationalCech.cechTotalInclusion V K p q n h :=
  HomologicalComplex₂.ιTotal_map (K := Rational.Cech.RationalCech.cechDoubleComplex U K)
    (L := Rational.Cech.RationalCech.cechDoubleComplex V K) (φ := cechDoubleComplexRefinement U V r hr K)
    (c₁₂ := ComplexShape.up ℕ) p q n h

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Refinement
