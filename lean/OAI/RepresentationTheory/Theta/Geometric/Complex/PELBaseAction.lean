import OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

/-! # PEL Base Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.PELBaseAction

noncomputable section

/-! The original integral model's action on the complex base is exactly
the prescribed reference embedding on every ring of integers element. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

include hg in
theorem complexPELBaseAction :
    D.complexPoint.appTop.hom.comp D.baseAction = Reference.LieSignature.referenceComplexBaseAction D.reference := by
  let j : AlgebraicGeometry.AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ℂ :=
    D.complexEmbedding.comp (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField K D.denominator D.denominator_ne_zero)
  have hj : Spec.map (CommRingCat.ofHom j) = D.complexPoint :=
    Spec.map_comp (CommRingCat.ofHom (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField K D.denominator
      D.denominator_ne_zero)) (CommRingCat.ofHom D.complexEmbedding)
  apply RingHom.ext
  intro a
  let b := algebraMap (NumberField.RingOfIntegers K) (AlgebraicGeometry.AbelianScheme.TateComparison.Data.modelRing K D.denominator)
    (NumberField.RingOfIntegers.mapRingHom D.fieldEmbedding a)
  have hb : j b = D.reference.μ (a : E) := by
    change D.complexEmbedding (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField K D.denominator
      D.denominator_ne_zero (algebraMap (NumberField.RingOfIntegers K) (AlgebraicGeometry.AbelianScheme.TateComparison.Data.modelRing K D.denominator)
        (NumberField.RingOfIntegers.mapRingHom D.fieldEmbedding a))) = _
    rw [ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap]
    exact congrArg (fun f : E →+* ℂ => f (a : E)) hg.embedding
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j)).symm b
  rw [hj] at hn
  exact hn.trans (congrArg (Scheme.ΓSpecIso (.of ℂ)).inv hb)

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.PELBaseAction
