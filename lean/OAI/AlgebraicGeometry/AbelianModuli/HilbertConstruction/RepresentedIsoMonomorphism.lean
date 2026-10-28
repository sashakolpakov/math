import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.UniversalLevelRigidity

/-! # Represented Iso Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedIsoMonomorphism

noncomputable section

/-! Every actual scheme representing the full polarized isomorphism functor at level at least three is a monomorphism over its locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem representedPolarizedIsoParameter_mono
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hN : 3 ≤ N)
    (M : Over S) (e : Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M) : Mono M.hom := by
  have hM (T : Over S) : Subsingleton (T ⟶ M) := by
    have hL : Subsingleton ((Family.LevelIsoFunctor.familyLevelIsoFunctor A B).obj (.op T)) :=
      LocallyNoetherian.UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_locallyNoetherian A B hN T
    exact (ConcreteCategory.bijective_of_isIso (e.inv.app (.op T))).injective.subsingleton
  constructor
  intro T f g hfg
  let U := Over.mk (f ≫ M.hom)
  let a : U ⟶ M := Over.homMk f rfl
  let b : U ⟶ M := Over.homMk g hfg.symm
  exact congrArg Over.Hom.left (@Subsingleton.elim (U ⟶ M) (hM U) a b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedIsoMonomorphism
