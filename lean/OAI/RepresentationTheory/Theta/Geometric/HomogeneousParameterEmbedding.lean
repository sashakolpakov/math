import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Homogeneous Parameter Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterEmbedding

noncomputable section

/-! Separation on all tests embeds the actual parameter scheme into
the concrete homogeneous Picard sheaf by its constructed line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem homogeneousParameterMap_mono
    {S : Scheme.{u}} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {P : Over S}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (hQ : A.IsHomogeneousPicardClass P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (hinj : ∀ T : Over S, Function.Injective (fun t : T ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t)) :
    Mono (ParameterizedHomogeneousPicard.homogeneousParameterMap A Q hQ) := by
  have (T : (Over S)ᵒᵖ) : Mono ((ParameterizedHomogeneousPicard.homogeneousParameterMap A Q hQ).app T) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro x y hxy
    apply ULift.ext
    apply hinj T.unop
    exact (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A Q hQ x.down).symm.trans
      ((congrArg (A.homogeneousPicardSheafInclusion.hom.app T) hxy).trans
        (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A Q hQ y.down))
  exact NatTrans.mono_of_mono_app _

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterEmbedding
