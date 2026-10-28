import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroSurjectivity

/-! # Degree Zero Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism

noncomputable section

/-! Actual global sections identify with degree-zero native Cech cohomology for every open cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

def cechTopSectionsHZeroIso
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) :
    F.obj.obj (op ⊤) ≅ ((cechComplexFunctor U).obj F.obj).homology 0 := by
  have : Mono (TopDegreeZero.cechTopSectionsToHZero U F) := TopDegreeZero.cechTopSectionsToHZero_mono U F hU
  have : Epi (TopDegreeZero.cechTopSectionsToHZero U F) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (DegreeZeroSurjectivity.cechTopSectionsToHZero_surjective U F hU)
  have : IsIso (TopDegreeZero.cechTopSectionsToHZero U F) := isIso_of_mono_of_epi _
  exact asIso (TopDegreeZero.cechTopSectionsToHZero U F)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism
