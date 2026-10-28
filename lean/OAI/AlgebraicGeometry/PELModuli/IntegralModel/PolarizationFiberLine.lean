import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Polarization Fiber Line -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationFiberLine.PolarizationAmpleness

noncomputable section

/-! HilbertConstruction's specified positivity on a geometric fiber implies ampleness
of the canonical Poincare diagonal bundle on that actual fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : A.scheme ⟶ D.abelian.scheme)
  {k : Type} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)

omit [IsAlgClosed k] in
theorem fiber_biextension_class :
    PolarizationLineAmpleness.PolarizationAmpleness.biextensionClass (D.pullback s) ((Over.pullback s).map ell) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D ell s) := by
  let t := ((Over.pullback s).map ell ⊗ₘ 𝟙 (A.pullback s).scheme).left
  have h := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp t (D.poincarePullbackOverMap s).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm
  have hm : t ≫ (D.poincarePullbackOverMap s).left = t ≫ AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D s :=
    congrArg (fun f => t ≫ f) (AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D s).symm
  exact h.trans (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) hm)

/-- The ample bundle witnessing positivity supplies the proof, but the
resulting ample bundle depends only on the given polarization and Poincare data. -/
theorem polarization_fiber_line_isAmple
    (hp : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D ell k s) :
    (PoincareClass.PoincareClasses.polarizationLine (D.pullback s) ((Over.pullback s).map ell)).IsAmple := by
  obtain ⟨L, hL, ⟨eZero⟩, ⟨eFormula⟩⟩ := hp
  let B := (A.pullback s).scheme
  have hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : B ⟶ B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := by
    have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass η[B].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (.of k)) := Quotient.sound ⟨eZero⟩
    have hu : (1 : B ⟶ B).left = B.hom ≫ η[B].left := rfl
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (1 : B ⟶ B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = _
    rw [hu, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
    rfl
  have hf : PolarizationLineAmpleness.PolarizationAmpleness.biextensionClass (D.pullback s) ((Over.pullback s).map ell) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst B B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd B B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[B].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
    rw [fiber_biextension_class]
    exact Quotient.sound ⟨eFormula⟩
  exact PolarizationLineAmpleness.PolarizationAmpleness.polarizationLine_isAmple_of_presentation (D.pullback s) ((Over.pullback s).map ell)
    L hL hzero hf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationFiberLine.PolarizationAmpleness
