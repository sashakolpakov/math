import OAI.NumberTheory.PadicHodge.IntegralComparison.DualCoordinateConormalBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalKoszulPurity

/-! # Differential Conormal Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialConormalBasis

noncomputable section

/-! A basis consisting of differentials of equations gives the
matching basis of their conormal module, through the dual derivations. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
  (I : Ideal A) {n : ℕ} (s : Fin n → A)
  (hs : Koszul.OrientedTopCohomology.ideal A s = I)
  (b : Module.Basis (Fin n) A Ω[A⁄k])
  (hb : (b : Fin n → Ω[A⁄k]) = fun i => KaehlerDifferential.D k A (s i))

def derivation (i : Fin n) : Derivation k A A :=
  (b.coord i).compDer (KaehlerDifferential.D k A)

include hb in
theorem dual (i j : Fin n) :
    derivation b i (ConormalKoszulPurity.conormalVectors A I s hs j).val =
      if i = j then 1 else 0 := by
  change b.coord i (KaehlerDifferential.D k A (s j)) = _
  rw [← congrFun hb j, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, eq_comm]

def basis : Module.Basis (Fin n) (A ⧸ I) I.Cotangent :=
  DualCoordinateConormalBasis.basis I
    (ConormalKoszulPurity.conormalVectors A I s hs)
    (derivation b) (dual I s hs b hb) hs

theorem basis_apply (i : Fin n) : basis I s hs b hb i =
    I.toCotangent (ConormalKoszulPurity.conormalVectors A I s hs i) :=
  DualCoordinateConormalBasis.basis_apply _ _ _ _ _ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialConormalBasis
