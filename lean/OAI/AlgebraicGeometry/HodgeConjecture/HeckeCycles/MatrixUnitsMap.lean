import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits

/-! # Matrix Units Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixUnitsMap.CM

noncomputable section

/-! Map invertible matrices through coefficient homomorphisms and
coordinate equivalences, retaining both inverse matrices explicitly. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I J R S : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [CommRing R] [CommRing S]

def map (e : I ≃ J) (f : R →+* S) : (Matrix I I R)ˣ →* (Matrix J J S)ˣ :=
  Units.map ((f.mapMatrix.comp (Matrix.reindexRingEquiv R e).toRingHom).toMonoidHom)

theorem map_val (e : I ≃ J) (f : R →+* S) (A : (Matrix I I R)ˣ) (i j : J) :
    (CM.map e f A).val i j = f (A.val (e.symm i) (e.symm j)) := rfl

theorem map_inv_val (e : I ≃ J) (f : R →+* S) (A : (Matrix I I R)ˣ) (i j : J) :
    ((CM.map e f A)⁻¹).val i j = f ((A⁻¹).val (e.symm i) (e.symm j)) := by
  rw [← map_inv, map_val]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixUnitsMap.CM
