import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureSerreMap

/-! # Mixed Pure Concentration Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureConcentrationCoordinates

noncomputable section

/-! The original mixed Serre concentration in degree zero agrees with
scalar-forgotten native Čech concentration, including the degree cast. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cast_concentration {C : Type*} [Category C]
    (A B : ℕ → C) (e : ∀ q, A q ≅ B q) {n m : ℕ} (h : n = m) :
    eqToIso (congrArg A h) ≪≫ e m = e n ≪≫ eqToIso (congrArg B h) := by
  subst m
  simp

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (haU : ∀ i, IsAffineOpen (U i))
  (N : X.Modules) (P : ChainComplex X.Modules ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex N P.op).X q).IsQuasicoherent]
  (c : ℕ)
  (hK : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N P.op).ExactAt q)

theorem zero :
    MixedPureSerreMap.concentration π U haU N P c hK 0 c (Nat.zero_add c).symm =
      Global.PureSectionNormalization.concentration π U haU
        (InternalHomCechTotal.internalComplex N P.op) c hK := by
  let K := InternalHomCechTotal.internalComplex N P.op
  let G := IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
  let T := (Cech.ConcentrationNaturality.totalFunctor π U).obj K
  let L := (Cech.ConcentrationNaturality.totalFunctor π U).obj
    ((single X.Modules (.up ℕ) c).obj (K.homology c))
  have hc := cast_concentration
    (fun q => ((G.mapHomologicalComplex (.up ℕ)).obj T).homology q)
    (fun q => G.obj (L.homology q))
    (fun q => Global.PureIntrinsicCoordinates.Intrinsic.concentration π U haU K c hK q)
    (Nat.zero_add c).symm
  apply Iso.ext
  have hd := congrArg (fun e => e.hom ≫
    G.map (OrderedCech.CechSingle.homologyIso π U (K.homology c) c 0).hom) hc
  simpa only [MixedPureSerreMap.concentration,
    InternalHomCechConcentration.totalHomologyIso,
    Cech.ConcentratedCohomology.iso,
    Global.PureSectionNormalization.concentration,
    Global.PureIntrinsicCoordinates.Intrinsic.concentration,
    IntrinsicOrdered.SingleEdge.Intrinsic.columnIso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, eqToIso.hom, eqToHom_map, K, G, T, L,
    IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars,
    InternalHomCechTotal.additiveTotal, InternalHomCechTotal.total,
    OrderedCech.Total.Comparison.bicomplex, Cech.ConcentrationNaturality.totalFunctor,
    Functor.comp_obj, HomologicalComplex₂.totalFunctor_obj] using hd

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedPureConcentrationCoordinates
