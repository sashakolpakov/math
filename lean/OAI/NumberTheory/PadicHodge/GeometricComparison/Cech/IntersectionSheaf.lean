import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover
import Mathlib.Topology.Sheaves.Functors

/-! # Intersection Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IntersectionSheaf.CechIntersectionSheaf

noncomputable section

/-! The native intersection presheaf of a module sheaf is the actual direct image of its open restriction, hence is already a sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (U : X.Opens)

def sheaf : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{u} R) U.ι.base).obj
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R U.ι).obj F)

def presheafIso : (sheaf R X F U).obj ≅ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X F.obj U :=
  NatIso.ofComponents (fun V => F.obj.mapIso (eqToIso (congrArg op (show
      U.ι ''ᵁ (U.ι ⁻¹ᵁ V.unop) = V.unop ⊓ U by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]))))
    (by
      intro V W f
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1)

theorem isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X F.obj U) :=
  (Presheaf.isSheaf_of_iso_iff (presheafIso R X F U)).mp (sheaf R X F U).property

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IntersectionSheaf.CechIntersectionSheaf
