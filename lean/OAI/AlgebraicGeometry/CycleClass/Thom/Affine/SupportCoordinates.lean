import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport

/-! # Support Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportCoordinates.Constructions

noncomputable section

/-! The native reduced-support prime is preserved by the actual affine
stalk coordinates, including the explicit identification of the affine
prime representing the chosen scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalStalk.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions.StalkCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem kernelPrime_coordinates (R : CommRingCat) (Y : Scheme) (e : Y ≅ Spec R)
    (A : IrreducibleCloseds Y) (B : IrreducibleCloseds (Spec R))
    (hAB : e.hom (IntersectionGeometry.supportPoint A) = IntersectionGeometry.supportPoint B) (y : Y) (hy : y ∈ (A : Set Y))
    (q : PrimeSpectrum R) (hq : e.hom y = q) (hqB : q ∈ (B : Set (Spec R))) :
    ((StalkPrimeQuotient.Constructions.kernelPrime Y A y hy).asIdeal).map (DiagonalStalk.Constructions.stalkCoordinateIsoAt R Y e y q hq).hom.hom =
      ((StalkPrimeQuotient.Constructions.kernelPrime (Spec R) B q hqB).asIdeal).map (Spec.stalkIso R q).hom.hom := by
  cases hq
  let k := e.hom.stalkMap y
  have hmap := Open.StalkSupport.Constructions.kernelPrime_map e.hom A B hAB y hy hqB
  have hi : (asIso k).inv.hom.comp k.hom = RingHom.id _ := by
    ext r
    exact (asIso k).hom_inv_id_apply r
  have hinv : ((StalkPrimeQuotient.Constructions.kernelPrime Y A y hy).asIdeal).map (asIso k).inv.hom =
      (StalkPrimeQuotient.Constructions.kernelPrime (Spec R) B (e.hom y) hqB).asIdeal := by
    rw [← hmap, Ideal.map_map, hi, Ideal.map_id]
  change ((StalkPrimeQuotient.Constructions.kernelPrime Y A y hy).asIdeal).map
    ((Spec.stalkIso R (e.hom y)).hom.hom.comp (asIso k).inv.hom) = _
  rw [← Ideal.map_map, hinv]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SupportCoordinates.Constructions
