import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GeneratedUniversalClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ClassificationTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyPoints

/-! # Universal Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalClassification

noncomputable section

/-! The specified quasi-projective Hilbert parameter and its actual universal family uniquely classify every smooth Hilbert family over arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem hilbertUniversalFamily_existsUnique_smooth
    {S : Scheme.{u}} {T : Over S} {n : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom] :
    ∃! g : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback g.left = F := by
  classical
  unfold Hilbert.ParameterScheme.hilbertUniversalFamily Hilbert.ParameterScheme.hilbertParameterScheme
  split_ifs with h
  · apply Hilbert.ClassificationTransport.hilbertClassifier_existsUnique_of_eq (ite_eq_left h)
    exact HilbertConstruction.Smooth.GeneratedUniversalClassification.generatedUniversalFamily_existsUnique_smooth F le_rfl
      (Hilbert.ParameterScheme.hilbertParameterTruncation_flat n P) (Hilbert.ParameterScheme.hilbertParameterTruncation_test n P) h
  · apply Hilbert.ClassificationTransport.hilbertClassifier_existsUnique_of_eq (ite_eq_right h)
    have : IsEmpty T.left := F.isEmpty_of_failedRankTest le_rfl h
    exact ⟨EmptyProjectiveParameters.overEmptySourceMap T (EmptyProjectiveParameters.emptyProjectiveParameter S), Subsingleton.elim _ _,
      fun g _ => EmptyProjectiveParameters.overEmptySourceMap_unique g _⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalClassification
