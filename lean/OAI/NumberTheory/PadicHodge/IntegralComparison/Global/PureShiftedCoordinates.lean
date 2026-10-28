import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureAdjunctionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureSerreMap

/-! # Pure Shifted Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureShiftedCoordinates

noncomputable section

/-! The original signed single-row identification turns native pure
total cohomology into the actual ordinary cohomology of its survivor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (haU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)

def concentration (g : ℕ) :=
  PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK (g+c) ≪≫
    (G).mapIso (OrderedCech.CechSingle.homologyIso π U (K.homology c) c g)

variable (N : X.Modules) (φ : K.homology c ⟶ N)

theorem map_single (g : ℕ) :
    (PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK (g+c)).hom ≫
      (G).map (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map
        ((single X.Modules (.up ℕ) c).map φ)) (g+c)) ≫
      (G).map (OrderedCech.CechSingle.homologyIso π U N c g).hom =
    (concentration π U haU K c hK g).hom ≫
      (G).map (homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map φ) g) := by
  have h := congrArg (G).map (OrderedCech.SingleNaturality.homology_naturality π U φ c g)
  simp only [Functor.map_comp] at h
  exact (congrArg
    ((PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK (g+c)).hom ≫ ·) h).trans
    (Category.assoc _ _ _).symm

variable (L : X.Modules) (P : ChainComplex X.Modules ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex L P.op).X q).IsQuasicoherent]
  (hP : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex L P.op).ExactAt q)

theorem internalHom (g : ℕ) :
    InternalHomCechConcentration.totalHomologyIso π U haU L P.op c hP g =
      concentration π U haU (InternalHomCechTotal.internalComplex L P.op) c hP g := by
  apply Iso.ext
  simp only [InternalHomCechConcentration.totalHomologyIso,
    Cech.ConcentratedCohomology.iso, concentration,
    PureIntrinsicCoordinates.Intrinsic.concentration,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureShiftedCoordinates
