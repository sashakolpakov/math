import Mathlib.RingTheory.Ideal.Maps

/-! # Ring Kernel Equiv Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RingKernelEquivTransport

noncomputable section

/-! A normalized ring square transfers the exact defining ideal through ring equivalences. -/

theorem ringKernel_eq_map_of_equiv_square
    {A S T S' T' : Type} [CommRing A] [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    (g : S →+* T) (g' : S' →+* T') (eS : S ≃+* S') (eT : T ≃+* T')
    (h : ∀ s, eT (g s) = g' (eS s))
    (a : A →+* S) (a' : A →+* S') (ha : eS.toRingHom.comp a = a')
    (I : Ideal A) (hI : RingHom.ker g' = Ideal.map a' I) :
    RingHom.ker g = Ideal.map a I := by
  have hk : RingHom.ker g = Ideal.comap eS.toRingHom (RingHom.ker g') := by
    ext s
    change g s = 0 ↔ g' (eS s) = 0
    rw [← h s, ← eT.map_zero]
    exact eT.injective.eq_iff.symm
  rw [hk, hI, ← ha, ← Ideal.map_map]
  exact Ideal.comap_map_of_bijective eS.toRingHom eS.bijective

end

end OAI.AlgebraicGeometry.Comparison.Betti.RingKernelEquivTransport
