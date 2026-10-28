import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClass

/-! # Pair Poincare Class Origin -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClassOrigin

noncomputable section

/-! Triviality on the dual-zero section makes the actual Poincare
class carry every zero point to the trivial homogeneous Picard class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g : ℕ} (A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.scheme ⊗ A.scheme).left)
    (h : A.IsHomogeneousPicardClass D.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))

theorem pairPoincareClass_origin
    (h₀ : Nonempty ((L.pullback (lift (1 : A.scheme ⟶ D.scheme) (𝟙 A.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)) (T : Over S) :
    A.homogeneousPicardSheaf.obj.map (1 : T ⟶ D.scheme).op (PairPoincareClass.pairPoincareClass A D L h) =
      A.trivialHomogeneousPicardClass T := by
  let z := lift (1 : A.scheme ⟶ D.scheme) (𝟙 A.scheme)
  let p := snd T A.scheme
  have hz : ((1 : T ⟶ D.scheme) ▷ A.scheme) = p ≫ z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [p, z]
  have hi : Nonempty ((L.pullback ((1 : T ⟶ D.scheme) ▷ A.scheme).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ A.scheme).left) :=
    ⟨(Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hz)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp p.left z.left).symm.app L.sheaf ≪≫
      (Scheme.Modules.pullback p.left).mapIso h₀.some ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p.left⟩
  have hq : A.homogeneousPicardPresheaf.map (1 : T ⟶ D.scheme).op
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L, h⟩ =
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A.scheme).left, A.trivialClass_homogeneous T⟩ :=
    Subtype.ext (Quotient.sound hi)
  exact ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).naturality_apply
    (1 : T ⟶ D.scheme).op ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L, h⟩).symm.trans
      (congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T)) hq)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClassOrigin
