import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology

/-! # Base Change Homology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeHomology

noncomputable section

/-! Flat scalar extension preserves homology as a module over the new ring,
including the full scalar action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

instance moduleBaseChange_preservesFiniteColimits :
    PreservesFiniteColimits (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B) := by
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  let G := ModuleCat.restrictScalars (algebraMap R B)
  have : PreservesFiniteColimits (F ⋙ G) :=
    preservesFiniteColimits_of_natIso (Base.ChangeTensorHomology.moduleBaseChangeRestrictionIso (R := R) (B := B))
  exact preservesFiniteColimits_of_reflects_of_preserves F G

instance moduleBaseChange_preservesFiniteLimits [Module.Flat R B] :
    PreservesFiniteLimits (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B) := by
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  let G := ModuleCat.restrictScalars (algebraMap R B)
  have : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_natIso (Base.ChangeTensorHomology.moduleBaseChangeRestrictionIso (R := R) (B := B))
  exact preservesFiniteLimits_of_reflects_of_preserves F G

def flatBaseChangeHomologyIso [Module.Flat R B]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).obj (C.homology q) ≅
      (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology q :=
  ((C.sc q).mapHomologyIso (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeHomology
