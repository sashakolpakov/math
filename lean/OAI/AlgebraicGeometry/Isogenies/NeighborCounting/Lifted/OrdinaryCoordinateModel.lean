import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear

/-! # Ordinary Coordinate Model -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinaryCoordinateModel.Ordinary

noncomputable section

/-! Package the actual ordinary lift and its generic block splitting
into the constructed integral coordinate model, retaining its special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj
      (OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l).X)

def liftedOrdinaryCoordinateModel :=
  let G := OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l
  let geometry := OrdinarySplitting.Ordinary.liftedActiveBlock_finiteLocallyFree j hsplit labels l
  letI : IsFinite G.X.hom := geometry.1
  letI : Flat G.X.hom := geometry.2.1
  letI : IsCommMonObj G.X := OrdinarySplitting.Ordinary.liftedActiveBlock_commutative j hsplit labels l
  OrdinaryCoordinateLinear.Lifts.constructOrdinaryCoordinateModel R L q G
    (OrdinarySplitting.Ordinary.liftedActiveOrdinaryGroupSplit j hsplit labels O l) eA
    (OrdinarySplitting.Ordinary.liftedActiveBlock_killed j hsplit labels l (Evaluated.Sections.Lifts.genericTest R L))
    (OrdinarySplitting.Ordinary.liftedActiveBlock_rank j hsplit labels O l
      (Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinaryCoordinateModel.Ordinary
