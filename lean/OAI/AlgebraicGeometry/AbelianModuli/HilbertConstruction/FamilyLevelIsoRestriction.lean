import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.LevelIsoFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismTransportEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.UniversalLevelRigidity

/-! # Family Level Iso Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyLevelIsoRestriction

noncomputable section

/-! Full-level rigidity makes the complete isomorphism functor compatible with restriction along every base map. The objectwise comparison is the actual composition isomorphism of polarized families. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def rigidFamilyLevelIsoRestriction
    {S U : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hN : 3 ≤ N) (i : U ⟶ S) :
    Family.LevelIsoFunctor.familyLevelIsoFunctor (A.pullback i) (B.pullback i) ≅ (Over.map i).op ⋙ Family.LevelIsoFunctor.familyLevelIsoFunctor A B :=
  NatIso.ofComponents
    (fun T => (Moduli.Isomorphisms.LevelPreservingIso.transportEquiv (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A i T.unop.hom)
      (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp B i T.unop.hom)).toIso)
    (by
      intro T V c
      apply ConcreteCategory.hom_ext
      intro e
      have hs : Subsingleton ((Family.LevelIsoFunctor.familyLevelIsoFunctor A B).obj (.op ((Over.map i).obj V.unop))) :=
        LocallyNoetherian.UniversalLevelRigidity.polarizedPullbackIsomorphisms_subsingleton_of_locallyNoetherian A B hN ((Over.map i).obj V.unop)
      exact @Subsingleton.elim _ hs _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyLevelIsoRestriction
