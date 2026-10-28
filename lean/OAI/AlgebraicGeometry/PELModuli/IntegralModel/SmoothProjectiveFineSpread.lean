import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FixedProjective
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericFamilyComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FineBaseChange
import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness

/-! # Smooth Projective Fine Spread -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveFineSpread

noncomputable section

/-! Smooth projective arithmetic base change preserves the actual fine PEL
classifier and constructs the exact spread with the supplied universal family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smooth_projective_arithmetic_fine_pel_spread
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    (Q : Over B.base) (hQ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Q.hom)
    (U : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Q)
    (hU : ∀ (T : Over B.base) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N T),
      ∃! f : T ⟶ Q, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data))
    [Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj Q).hom]
    (PQ : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj Q).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj Q).hom)
    (hN : N ≠ 0) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) :
    ∃ C : Base.ArithmeticBaseExtension K κ, IsUnit (N : C.R) ∧
      ∃ T : PEL.Has.IntegralPELSpread P iota κ N M.space M.universal C,
        T.IsReducedPELModuli P ∧ Smooth T.toOver.hom ∧ IsProper T.toOver.hom ∧
          Components.RelativelyProjective T.toOver := by
  let : Algebra B.R ℂ := (B.embedding.comp B.toField).toAlgebra
  let i : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj Q ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ PQ.ambientDimension := Over.homMk PQ.embedding PQ.over_base
  have : IsClosedImmersion i.left := PQ.closedImmersion
  obtain ⟨D, hdiv, φ, hφ, hsm, hp, hproj⟩ :=
    Arithmetic.FixedProjective.arithmetic_fixed_smooth_projective_model B rfl Q hQ PQ.ambientDimension i N hN
  let C := B.compose D
  let Q' := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q
  have : Smooth Q'.hom := hsm
  have : IsReduced Q'.left :=
    ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction.smooth_model_reduced_of_injective_generic C.toField C.toField_injective Q'
  let V : PEL.Has.IntegralPELObject P C.R (C.integralEmbedding iota) N Q' :=
    (U.baseChange φ).changeEmbedding (B.compose_integralEmbedding D φ hφ iota)
  have hV : ∀ (T : Over C.base) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P C.R (C.integralEmbedding iota) N T),
      ∃! f : T ⟶ Q', Nonempty (PEL.Iso.PolarizedActionIso (V.pullback f).data A.data) :=
    IntegralPEL.FineComparison.integralPEL_fine_changeEmbedding (U.baseChange φ) (B.compose_integralEmbedding D φ hφ iota)
      (IntegralPEL.FineBaseChange.integralPEL_fine_baseChange U hU φ)
  exact ⟨C, C.divisor_isUnit N hdiv, Arithmetic.GenericFamilyComparison.integralPELSpreadOfFineModel C V M hV hM,
    Arithmetic.GenericFamilyComparison.integralPELSpreadOfFineModel_isReducedPELModuli C V M hV hM, hsm, hp, hproj⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveFineSpread
