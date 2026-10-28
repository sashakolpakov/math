import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Homogeneous Parameter Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousParameterRecovery

noncomputable section

/-! Exact recovery of a line class recovers its homogeneous Picard
parameter map on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

theorem homogeneousParameterClass_identity {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (V : Over S) (L : HilbertConstruction.Line.Bundles.LineBundle (V ⊗ A.scheme).left)
    (hL : A.IsHomogeneousPicardClass V (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A L hL (𝟙 V) =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op V)
        ⟨HilbertConstruction.Line.Bundles.LineBundle.classOf L, hL⟩ := by
  apply congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op V))
  apply Subtype.ext
  exact (congrArg (fun m : V ⊗ A.scheme ⟶ V ⊗ A.scheme => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass m.left (HilbertConstruction.Line.Bundles.LineBundle.classOf L))
    (id_tensorHom_id V A.scheme)).trans (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (HilbertConstruction.Line.Bundles.LineBundle.classOf L))

theorem homogeneousParameterClass_of_recovery {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {V W : Over S} (L : HilbertConstruction.Line.Bundles.LineBundle (W ⊗ A.scheme).left) (J : HilbertConstruction.Line.Bundles.LineBundle (V ⊗ A.scheme).left)
    (hL : A.IsHomogeneousPicardClass W (HilbertConstruction.Line.Bundles.LineBundle.classOf L))
    (hJ : A.IsHomogeneousPicardClass V (HilbertConstruction.Line.Bundles.LineBundle.classOf J)) (q : V ⟶ W)
    (hr : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = HilbertConstruction.Line.Bundles.LineBundle.classOf J)
    {T : Over S} (a : T ⟶ V) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A L hL (a ≫ q) = RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ a := by
  have hq : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass L q = HilbertConstruction.Line.Bundles.LineBundle.classOf J :=
    (congrArg (fun m : V ⊗ A.scheme ⟶ W ⊗ A.scheme => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass m.left (HilbertConstruction.Line.Bundles.LineBundle.classOf L))
      (tensorHom_id q A.scheme)).trans hr
  apply congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T))
  apply Subtype.ext
  exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_naturality L q a).symm.trans
    (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A.scheme).left) hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousParameterRecovery
