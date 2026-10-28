import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Level Comparison -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LevelComparison.Abelian

noncomputable section

/-!
Constant ordered labels detect equality of the complete full-level
natural isomorphism, including its values on disconnected test schemes.
Their actual fiber values are the base changes of algebraic sections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem fullLevel_eq_of_constant_sections
    {S : Scheme} {g n : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (level₁ level₂ : A.FullLevel n)
    (h : ∀ a : Multiplicative (Fin (2 * g) → ZMod n),
      (level₁.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S a)).val =
      (level₂.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S a)).val) :
    level₁ = level₂ := by
  apply level₁.changeEquiv.injective
  apply Iso.ext
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupMap_ext
  intro s
  apply MonoidHom.ext
  intro a
  change LocallyConstant.toFun
    (level₁.inv.app (.op (Over.mk (𝟙 S)))
      (level₁.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S a))) s =
    LocallyConstant.toFun
    (level₁.inv.app (.op (Over.mk (𝟙 S)))
      (level₂.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S a))) s
  exact congrArg (fun u : A.torsionPoints n (Over.mk (𝟙 S)) =>
    LocallyConstant.toFun (level₁.inv.app (.op (Over.mk (𝟙 S))) u) s) (Subtype.ext (h a))

theorem fullLevel_transport_eq_of_constant_sections
    {S : Scheme} {g n : ℕ} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (level₁ : A.FullLevel n) (level₂ : B.FullLevel n)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (h : ∀ a : Multiplicative (Fin (2 * g) → ZMod n),
      (level₁.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S a)).val ≫ e.hom =
      (level₂.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S a)).val) :
    level₁.transport e = level₂ :=
  fullLevel_eq_of_constant_sections _ _ h

namespace FamilyPoints

theorem fullLevel_pullback_constant_section
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g n : ℕ} (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (level : G.FullLevel n) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (a : Multiplicative (Fin (2 * g) → ZMod n)) :
    ((level.pullback s.left).hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val =
    FamilyTranslations.Abelian.FamilyPoints.fiberSection S G
      ((level.hom.app (.op (Over.mk (𝟙 S.left)))) (LocallyConstant.const S.left a)).val s := by
  let T := (Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
  have h := ConcreteCategory.congr_hom (level.hom.naturality (FamilyTranslations.Abelian.FamilyPoints.sectionBasePoint S s).op)
    (LocallyConstant.const S.left a)
  have hv := congrArg (fun u : G.torsionPoints n T => u.val) h
  change (level.hom.app (.op T) (LocallyConstant.const T.left a)).val =
    FamilyTranslations.Abelian.FamilyPoints.sectionBasePoint S s ≫
      (level.hom.app (.op (Over.mk (𝟙 S.left))) (LocallyConstant.const S.left a)).val at hv
  exact congrArg (G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).symm hv

end FamilyPoints

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LevelComparison.Abelian
