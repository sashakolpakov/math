import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

/-! # Support Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportBaseChange

noncomputable section

/-! Native affine support modules commute with base change whenever
the extended support ideal is prime. The stalk maps are the actual
maps induced by the affine scheme morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable (R S : Type) [CommRing R] [CommRing S] (f : R →+* S)
  (q : PrimeSpectrum R) (hq : (q.asIdeal.map f).IsPrime) (p : PrimeSpectrum S)
  (hqp : q.asIdeal.map f ≤ p.asIdeal)

theorem ideal :
    (q.asIdeal.map (StructureSheaf.toStalk R (PrimeSpectrum.comap f p)).hom).map
      ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom =
      (q.asIdeal.map f).map (StructureSheaf.toStalk S p).hom := by
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg (fun g : R →+* (Spec (.of S)).presheaf.stalk p => q.asIdeal.map g)
    (congrArg CommRingCat.Hom.hom (AlgebraicGeometry.stalkMap_toStalk (CommRingCat.ofHom f) p))

def equiv :
    letI : Algebra ((Spec (.of R)).presheaf.stalk (PrimeSpectrum.comap f p))
      ((Spec (.of S)).presheaf.stalk p) := ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom.toAlgebra
    (Flat.Extension.baseChange ((Spec (.of R)).presheaf.stalk (PrimeSpectrum.comap f p))
      ((Spec (.of S)).presheaf.stalk p)).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (SupportStalk.support R q) (PrimeSpectrum.comap f p)
          (SupportStalk.mem R q (PrimeSpectrum.comap f p) (Ideal.map_le_iff_le_comap.mp hqp))) ≃ₗ[(Spec (.of S)).presheaf.stalk p]
      CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of S)) (SupportStalk.support S ⟨q.asIdeal.map f, hq⟩) p
        (SupportStalk.mem S ⟨q.asIdeal.map f, hq⟩ p hqp) := by
  let A := (Spec (.of R)).presheaf.stalk (PrimeSpectrum.comap f p)
  let B := (Spec (.of S)).presheaf.stalk p
  let : Algebra A B := ((Spec.map (CommRingCat.ofHom f)).stalkMap p).hom.toAlgebra
  let I := q.asIdeal.map (StructureSheaf.toStalk R (PrimeSpectrum.comap f p)).hom
  let eR := SupportStalk.moduleEquiv R q (PrimeSpectrum.comap f p) (Ideal.map_le_iff_le_comap.mp hqp)
  let eS := SupportStalk.moduleEquiv S ⟨q.asIdeal.map f, hq⟩ p hqp
  exact ((Flat.Extension.baseChange A B).mapIso eR.toModuleIso).toLinearEquiv.trans
    ((Ideal.qoutMapEquivTensorQout (R := A) (I := I) B).symm.trans
      ((Submodule.quotEquivOfEq _ _ (ideal R S f q p)).trans eS.symm))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportBaseChange
