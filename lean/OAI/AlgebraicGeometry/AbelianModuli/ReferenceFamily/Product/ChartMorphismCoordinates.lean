import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinates

/-! # Chart Morphism Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartMorphismCoordinates

noncomputable section

section

/-! An original morphism between two dual families acquires product
coordinates by conjugating with their actual affine product charts.
Its reduction is the original fixed-fiber map. -/

open scoped TensorProduct

variable {k A B S T : Type} [CommRing k] [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra k A] [Algebra k B]
    [Algebra (DualNumber k) S] [Algebra (DualNumber k) T]
    (f : S →ₐ[DualNumber k] T)
    (r : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (s : T ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))

def productChartMorphismCoordinates :
    (DualNumber k ⊗[k] A) →ₐ[DualNumber k] (DualNumber k ⊗[k] B) :=
  s.toAlgHom.comp (f.comp r.symm.toAlgHom)

theorem productChartMorphismCoordinates_reduction
    (qS : S →+* A) (qT : T →+* B) (q : A →ₐ[k] B)
    (hr : ∀ x, Dual.TensorReduction.dualTensorReduction k A (r x) = qS x)
    (hs : ∀ x, Dual.TensorReduction.dualTensorReduction k B (s x) = qT x)
    (hf : ∀ x, qT (f x) = q (qS x))
    (u : DualNumber k ⊗[k] A) :
    Dual.TensorReduction.dualTensorReduction k B (productChartMorphismCoordinates f r s u) =
      q (Dual.TensorReduction.dualTensorReduction k A u) := by
  change Dual.TensorReduction.dualTensorReduction k B (s (f (r.symm u))) = _
  rw [hs, hf]
  have h := hr (r.symm u)
  rw [r.apply_symm_apply] at h
  exact congrArg q h.symm

end

/-! An original commuting square of dual-family algebra maps stays
commutative in any of their actual reference product charts. -/

open scoped TensorProduct

variable {k A A' B B' S S' T T' : Type} [CommRing k]
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
    [Algebra k A] [Algebra k A'] [Algebra k B] [Algebra k B']
    [Algebra (DualNumber k) S] [Algebra (DualNumber k) S']
    [Algebra (DualNumber k) T] [Algebra (DualNumber k) T']

theorem productChartMorphism_square
    (f : S →ₐ[DualNumber k] T) (f' : S' →ₐ[DualNumber k] T')
    (p : S →ₐ[DualNumber k] S') (q : T →ₐ[DualNumber k] T')
    (r : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (r' : S' ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A'))
    (s : T ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (s' : T' ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B'))
    (h : q.comp f = f'.comp p) :
    (productChartMorphismCoordinates q s s').comp (productChartMorphismCoordinates f r s) =
      (productChartMorphismCoordinates f' r' s').comp (productChartMorphismCoordinates p r r') := by
  apply AlgHom.ext
  intro u
  change s' (q (s.symm (s (f (r.symm u))))) = s' (f' (r'.symm (r' (p (r.symm u)))))
  rw [s.symm_apply_apply, r'.symm_apply_apply]
  exact congrArg s' (AlgHom.congr_fun h (r.symm u))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartMorphismCoordinates
