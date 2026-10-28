import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Open Chart Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compose actual pointed open charts without changing the boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {k R S : Type u} {ι : Type v} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

def Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart.comp {v : ι → S} {q : PrimeSpectrum S}
    (C : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of S) v q) (f : R →ₐ[k] S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (w : ι → R) (hw : ∀ j, f (w j) = v j) (p : PrimeSpectrum R)
    (hq : PrimeSpectrum.comap f.toRingHom q = p) :
    Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of R) w p := by
  refine { carrier := C.carrier
           algebra := C.algebra
           map := C.map.comp f
           isOpenImmersion := ?_
           point := C.point
           point_over := ?_
           model := ?_ }
  · change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom C.map.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change C.point.asIdeal.comap (C.map.toRingHom.comp f.toRingHom) = p.asIdeal
    have hC : C.point.asIdeal.comap C.map.toRingHom = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal C.point_over
    have hq' : q.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [← Ideal.comap_comap, hC, hq']
  · have he : (fun j => (C.map.comp f) (w j)) = (fun j => C.map (v j)) := by
      funext j
      exact congrArg C.map (hw j)
    rw [he]
    exact C.model

end

end OAI.AlgebraicGeometry.Resolution.Blowups
