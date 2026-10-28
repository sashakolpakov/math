import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix

/-! Concrete original-variable layouts with every produced integer row retained.
The rank basis is used only to count attained signatures. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSource

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets

variable {r Q D n R : ℕ} {F O : Type*} [CommRing O] {node : Fin Q → O}

/-- Universal rows are assembled on incidences and then summed along the
original owner fibers. No Boolean variable is introduced by this construction. -/
noncomputable def canonicalData
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (factor : Fin D → F)
    (head : Fin Q → Fin n → Fin r) (color : F → Fin Q → Fin r)
    (hhead : ∀ i t, (P.label i).head t = head t (owner i))
    (hcolor : ∀ i t, (P.label i).slot 0 t = color (factor i) t)
    (A : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) :
    Layout.Data (O := O) (G := Fin r) owner factor Q R :=
  LayoutHeadPullback.pullback owner factor head
    (LayoutBlocks.data (LayoutUniversal.data A R denom hdenom units)
      P.completeBlocks factor color hcolor) (fun t i => hhead i t)

/-- The producer's raw matrix has one row per incidence, including zero and
repeated rows. Its constraints determine exactly the required foreign values. -/
noncomputable def data
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (factor : Fin D → F)
    (head : Fin Q → Fin n → Fin r) (color : F → Fin Q → Fin r)
    (hhead : ∀ i t, (P.label i).head t = head t (owner i))
    (hcolor : ∀ i t, (P.label i).slot 0 t = color (factor i) t)
    (A : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) :
    Layout.Data (O := O) (G := Fin r) owner factor Q R where
  node := node
  units := units
  head := head
  color := color
  row := (canonicalData P owner factor head color hhead hcolor A denom hdenom units).row
  row_origin :=
    (canonicalData P owner factor head color hhead hcolor A denom hdenom units).row_origin
  row_degree :=
    (canonicalData P owner factor head color hhead hcolor A denom hdenom units).row_degree
  rowCount := fun _ _ => D
  constraints := fun t _ j v => LayoutProducedMatrix.literalMatrix P owner A R t j v.val
  locality := by
    intro t i g hg z hz
    let C := LayoutUniversal.data (r := r) A R denom hdenom units
    let o := LayoutProducedMatrix.headOwner P owner head hhead t g
    have hp : ∀ j, signature
        (pulledConstraints o (LayoutProgram.paddedConstraint P A R t g)) z j = 0 := by
      intro j
      convert hz j using 1
      apply Finset.sum_congr rfl
      intro v _
      exact congrArg (fun a : ℤ => a * z v)
        (LayoutProducedMatrix.literalMatrix_head P owner head hhead A R t g j v).symm
    have hc := integer_kernel_of_rational_span _ _
      (LayoutProgram.paddedConstraint_pullback_spans P A R denom hdenom units t g o).1
      z hp
    apply (canonicalData P owner factor head color hhead hcolor A denom hdenom units).locality
      t i g hg z
    intro j
    exact hc ((Fintype.equivFin (LayoutBlocks.RowIndex C P.completeBlocks t g)).symm j)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutSource
