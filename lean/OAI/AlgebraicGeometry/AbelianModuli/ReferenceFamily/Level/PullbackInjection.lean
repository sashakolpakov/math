import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleDescentLocal

/-! # Pullback Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.PullbackInjection

noncomputable section

/-! An ordered full level is detected after a surjective base change,
using its actual locally constant change-of-basis labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.ParameterBaseChange

theorem fullLevel_pullback_injective {S T : Scheme.{0}} {g N : ℕ} [NeZero N]
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S) [Surjective u] :
    Function.Injective (fun α : A.FullLevel N => α.pullback u) := by
  intro α β h
  apply α.labelsEquiv.injective
  have he : (α.labelsEquiv α).comap ⟨u, u.continuous⟩ =
      (α.labelsEquiv β).comap ⟨u, u.continuous⟩ :=
    (HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_pullback α α u).symm.trans
      ((congrArg (α.pullback u).labelsEquiv h).trans (HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_pullback α β u))
  apply LocallyConstant.ext
  intro s
  obtain ⟨t, ht⟩ := u.surjective s
  exact ht ▸ congrArg (fun b : LocallyConstant T (HilbertConstruction.Level.Parameters.LevelLabelAut g N) => b t) he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.PullbackInjection
