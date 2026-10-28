import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineOn
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange

/-! # Positive Line Formula Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineFormulaTransport

noncomputable section

/-! Transport the actual ample Poincare formula through a native
group isomorphism, using its precise recovered line class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem positiveLineFormula_pullback
    {S : Scheme.{0}} {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] [IsIso f]
    (P : HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left) (Q : HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ B.scheme).left)
    (hQ : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ⊗ₘ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = HilbertConstruction.Line.Bundles.LineBundle.classOf P)
    (hpos : PositiveLineOn.PositiveLineFormula B Q) : PositiveLineOn.PositiveLineFormula A P := by
  obtain ⟨L, hL, hz, hm⟩ := (PositiveLineOn.positiveLineFormula_iff_class B Q).mp hpos
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  apply (PositiveLineOn.positiveLineFormula_iff_class A P).mpr
  refine ⟨L.pullback f.left, hL.pullback_of_isIso f.left, ?_, ?_⟩
  · exact (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp η[A.scheme].left f.left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun a => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (HilbertConstruction.Line.Bundles.LineBundle.classOf L))
        (congrArg Over.Hom.left (IsMonHom.one_hom f))).trans hz)
  · have h₁ := PicardSquareComparison.picardPullback_square (f ⊗ₘ f).left (fst B.scheme B.scheme).left
      (fst A.scheme A.scheme).left f.left (Over.tensorHom_left_fst _ _ f f) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)
    have h₂ := PicardSquareComparison.picardPullback_square (f ⊗ₘ f).left (snd B.scheme B.scheme).left
      (snd A.scheme A.scheme).left f.left (Over.tensorHom_left_snd _ _ f f) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)
    have h₃ := PicardSquareComparison.picardPullback_square (f ⊗ₘ f).left μ[B.scheme].left
      μ[A.scheme].left f.left (congrArg Over.Hom.left (IsMonHom.mul_hom f)).symm (HilbertConstruction.Line.Bundles.LineBundle.classOf L)
    have hh := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ⊗ₘ f).left) hm
    rw [map_mul, map_mul, hQ, h₁, h₂, h₃] at hh
    exact hh

theorem positiveLineFormula_transport
    {S : Scheme.{0}} {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (P : HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left) (Q : HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ B.scheme).left)
    (hQ : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (e.hom ⊗ₘ e.hom).left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = HilbertConstruction.Line.Bundles.LineBundle.classOf P)
    (hpos : PositiveLineOn.PositiveLineFormula A P) : PositiveLineOn.PositiveLineFormula B Q := by
  let e₂ : (A.scheme ⊗ A.scheme).left ≅ (B.scheme ⊗ B.scheme).left :=
    (Over.forget S).mapIso (tensorIso e e)
  have hr : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (e.inv ⊗ₘ e.inv).left (HilbertConstruction.Line.Bundles.LineBundle.classOf P) = HilbertConstruction.Line.Bundles.LineBundle.classOf Q :=
    PicardSquareComparison.picardPullback_inverse e₂ (HilbertConstruction.Line.Bundles.LineBundle.classOf P) (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) hQ
  exact positiveLineFormula_pullback B A e.inv Q P hr hpos

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineFormulaTransport
