import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.Parameter
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.QuasiProjectivity

noncomputable section

/-! Over a noetherian base, the actual smooth Hilbert parameter has a quasi-projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

def smoothHilbertParameterQuasiProjectivePresentation
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Parameter.smoothHilbertParameter S n P) := by
  let M := Hilbert.ParameterScheme.hilbertParameterScheme S n P
  let Q := Hilbert.ParameterScheme.hilbertParameterQuasiProjectivePresentation S n P
  let U := (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).smoothBaseOpen
  have : LocallyOfFiniteType M.hom := Q.locallyFiniteType
  have : QuasiCompact M.hom := Q.quasiCompact
  have : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  have : CompactSpace M.left := QuasiCompact.compactSpace_of_compactSpace M.hom
  have : IsNoetherian M.left := ⟨⟩
  have : NoetherianSpace M.left := IsNoetherian.noetherianSpace
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set M.left)
  have : QuasiCompact U.ι := inferInstance
  have : IsOpenImmersion (Parameter.smoothHilbertParameterInclusion S n P).left :=
    inferInstanceAs (IsOpenImmersion U.ι)
  refine
    { locallyFiniteType := ?_
      quasiCompact := ?_
      compactification := Q.compactification
      projective := Q.projective
      embedding := Parameter.smoothHilbertParameterInclusion S n P ≫ Q.embedding
      openImmersion := ?_ }
  · change LocallyOfFiniteType (U.ι ≫ M.hom)
    infer_instance
  · change QuasiCompact (U.ι ≫ M.hom)
    infer_instance
  · change IsOpenImmersion ((Parameter.smoothHilbertParameterInclusion S n P).left ≫ Q.embedding.left)
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.QuasiProjectivity
