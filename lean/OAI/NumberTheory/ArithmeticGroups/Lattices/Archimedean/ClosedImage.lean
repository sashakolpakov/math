import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ExteriorAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation

/-! # Closed Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ClosedImage.Construction

noncomputable section

/-! The full archimedean realization of a connected semisimple matrix
group has closed image in the ambient special-linear arithmetic
quotient. This uses the proved integral fixed-vector construction. -/

open scoped Classical _root_.NumberField
open _root_.NumberField MulAction

theorem fullArchimedeanMatrixGroup_quotient_image_closed
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    IsClosed ((QuotientGroup.mk : ExteriorAction.Construction.FullArchimedeanSL k n →
      ExteriorAction.Construction.FullArchimedeanSL k n ⧸ ExteriorAction.Construction.fullArchimedeanIntegralSL k n) ''
        (ExteriorAction.Construction.fullArchimedeanMatrixGroup G : Set (ExteriorAction.Construction.FullArchimedeanSL k n))) := by
  obtain ⟨d, r, x, hx, hfixed⟩ := CoordinateIntegralVector.Construction.exists_integral_coordinate_vector_stabilizer (R := 𝓞 k) G hconn hsemi
  let := ExteriorAction.Construction.archimedeanExteriorAction k n d r
  let := ExteriorAction.Construction.continuous_archimedeanExteriorAction k n d r
  let Λ := CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice (R := 𝓞 k) (k := k) n d r
  let L := AdeleCoordinateLattice.Construction.coordinateAdeleLattice Λ
  let xA := AdeleCoordinateLattice.Construction.coordinateAdeleEmbedding k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r) x
  have hG : ExteriorAction.Construction.fullArchimedeanMatrixGroup G = stabilizer (ExteriorAction.Construction.FullArchimedeanSL k n) xA := by
    ext g
    change (∀ v, g v ∈ G.subgroup v.Completion (algebraMap k v.Completion)) ↔ g • xA = xA
    constructor
    · intro hg
      funext v
      exact ((hfixed v.Completion).2 (g v)).mp (hg v)
    · intro hg v
      exact ((hfixed v.Completion).2 (g v)).mpr (congrFun hg v)
  have hfg : Λ.FG := CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice_fg n d r
  have hclosed : IsClosed (L : Set (AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r))) :=
    AdeleCoordinateLattice.Construction.coordinateAdeleLattice_closed Λ hfg
  have hdisc : IsDiscrete (L : Set (AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r))) :=
    isDiscrete_iff_discreteTopology.mpr (AdeleCoordinateLattice.Construction.coordinateAdeleLattice_discrete Λ hfg)
  rw [hG]
  exact StabilizerSaturation.Construction.stabilizer_image_closed_of_discrete_invariant_set (ExteriorAction.Construction.fullArchimedeanIntegralSL k n) xA
    L hclosed hdisc ⟨x, hx, rfl⟩ ExteriorAction.Construction.archimedeanIntegralSL_preserves_exterior_lattice

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ClosedImage.Construction
