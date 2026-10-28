import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupPointData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.AbelianParameters

/-! # Point Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData

noncomputable section

/-! The concrete abelian parameter classifies Hilbert data with actual bounded commutative-group operations and geometrically connected fibers on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

def FixedDimensionHilbertAbelianData (T : Over S) :=
  {D : GroupPointData.FixedDimensionHilbertGroupData S n P g Pm Pi T // GeometricallyConnected (D.family S n P g Pm Pi).hom}

def FixedDimensionHilbertAbelianData.abelianScheme {T : Over S}
    (D : FixedDimensionHilbertAbelianData S n P g Pm Pi T) : Abelian.Schemes.AbelianScheme g T.left where
  scheme := D.val.family S n P g Pm Pi
  group := D.val.groupObj S n P g Pm Pi
  commutative := D.val.groupObj_comm S n P g Pm Pi
  proper := (D.val.projective S n P g Pm Pi).proper
  smoothDimension := D.val.dimension S n P g Pm Pi
  connected := D.property

def fixedDimensionHilbertAbelianNativePointEquiv (T : Over S) :
    (T ⟶ AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) ≃
      FixedDimensionHilbertAbelianData S n P g Pm Pi T :=
  (AbelianParameters.fixedDimensionHilbertAbelianParameterPointEquiv S n P g Pm Pi T).trans
    ((GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T).subtypeEquiv
      (GroupPointData.fixedDimensionHilbertGroupPoint_connected_iff S n P g Pm Pi T))

theorem fixedDimensionHilbertAbelian_quasiProjective_native_classification :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      ∀ T : Over S, Nonempty ((T ⟶ M) ≃ FixedDimensionHilbertAbelianData S n P g Pm Pi T) :=
  ⟨AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
    ⟨AbelianParameters.fixedDimensionHilbertAbelianParameterQuasiProjectivePresentation S n P g Pm Pi⟩,
    fun T => ⟨fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData
