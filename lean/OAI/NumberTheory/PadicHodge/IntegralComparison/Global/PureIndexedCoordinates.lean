import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureShiftedCoordinates

/-! # Pure Indexed Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIndexedCoordinates

noncomputable section

/-! The original shifted concentration retains an explicit equality
of total degrees, as used by the fixed projective trace construction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (haU : ∀ i, IsAffineOpen (U i))
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)

def singleIso (N : X.Modules) (c g q : ℕ) (hq : q=g+c) :=
  eqToIso (congrArg (fun k => (G).obj
    (((Cech.ConcentrationNaturality.totalFunctor π U).obj
      ((single X.Modules (.up ℕ) c).obj N)).homology k)) hq) ≪≫
    (G).mapIso (OrderedCech.CechSingle.homologyIso π U N c g)

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

def concentration (g q : ℕ) (hq : q=g+c) :=
  eqToIso (congrArg (fun k => (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.nativeFunctor π U k).obj K) hq) ≪≫
    PureShiftedCoordinates.concentration π U haU K c hK g

variable (N : X.Modules) (φ : K.homology c ⟶ N)

theorem map_single (g q : ℕ) (hq : q=g+c) :
    (PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK q).hom ≫
      (G).map (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map
        ((single X.Modules (.up ℕ) c).map φ)) q) ≫
      (singleIso π U N c g q hq).hom =
    (concentration π U haU K c hK g q hq).hom ≫
      (G).map (homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map φ) g) := by
  subst q
  simpa only [singleIso, concentration, eqToIso_refl, Iso.refl_trans, Functor.mapIso_hom] using
    PureShiftedCoordinates.map_single π U haU K c hK N φ g

variable (L : X.Modules) (P : ChainComplex X.Modules ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex L P.op).X q).IsQuasicoherent]
  (hP : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex L P.op).ExactAt q)

theorem internalHom (g q : ℕ) (hq : q=g+c) :
    MixedPureSerreMap.concentration π U haU L P c hP g q hq =
      concentration π U haU (InternalHomCechTotal.internalComplex L P.op) c hP g q hq := by
  subst q
  simpa only [MixedPureSerreMap.concentration, concentration,
    eqToIso_refl, Iso.refl_trans] using
      PureShiftedCoordinates.internalHom π U haU c L P hP g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIndexedCoordinates
