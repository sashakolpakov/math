import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DivisionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers

/-! # Lattice Level Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeLevelComparison

noncomputable section

/-! Preservation of the canonical lattice labels modulo N implies
every original full-level equation on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g N : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)

theorem level_comparison_of_native_lattice [NeZero N]
    (α : A.FullLevel N) (β : B.FullLevel N) (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (hf : ∀ c, LatticeDivision.TorusTorsion.modNMap N (DivisionNaturality.originalLatticeMap A B PA PB f).toAddMonoidHom
      (OrderedLatticeLevel.nativeOrderedLatticeLevel A PA α c) = OrderedLatticeLevel.nativeOrderedLatticeLevel B PB β c)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients g N)) :
    (α.hom.app (.op T) c).val ≫ f = (β.hom.app (.op T) c).val := by
  apply Level.Stabilizers.LevelCover.level_comparison_of_base_constants α β f ?_ T c
  intro a
  have hn := DivisionNaturality.nativeDivisionEquiv_natural A B PA PB f (OrderedLatticeLevel.nativeOrderedLatticeLevel A PA α a.toAdd)
  have ha := congrArg (fun v : Additive (A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) => v.toMul.val ≫ f)
    (OrderedLatticeLevel.nativeDivisionEquiv_ordered A PA α a.toAdd)
  have hb := congrArg (fun v : Additive (B.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) => v.toMul.val)
    (OrderedLatticeLevel.nativeDivisionEquiv_ordered B PB β a.toAdd)
  have he := congrArg (fun q => (OrderedLatticeLevel.nativeDivisionEquiv B PB q).toMul.val) (hf a.toAdd)
  exact (hn.trans ha).symm.trans (he.trans hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LatticeLevelComparison
